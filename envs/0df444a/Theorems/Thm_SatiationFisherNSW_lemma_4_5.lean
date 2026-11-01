-- Prove2me | Theorems.Thm_SatiationFisherNSW_lemma_4_5
-- name    : SatiationFisherNSW.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:52.733093+00:00
-- url     : https://prove2.me/theorems/457aa338-9532-4351-811f-a6043b4a3661
-- title:
--   Lemma 4.5 — tree sizes after Rounding (a), and goods of price above $1$
-- statement:
--   Under the standing assumptions of §4.1, consider any run of the rounding procedure and a tree component $T$ of $(B\setminus B_0)\times(G\setminus G_0)$ after step (a) of rounding. Then $T$ has $k_T+1$ agents and $k_T$ goods for some $k_T\ge0$.
--
--   Moreover, suppose agent $i$ of $T$ is assigned a good $j$ with $p_j>1$ during step (a) of rounding. Then
--
--   1. $i$ spends all its money on $j$: $p_jx_{ij}=1$;
--   2. $i$ is the only agent that spends money on $j$: $p_jx_{i'j}=0$ for $i'\neq i$;
--   3. the valuation of $i$ after rounding is exactly $p_j$;
--   4. $B_c\cap T=\emptyset$: no agent of $T$ is capped in $(x,p)$.
--
--   Differences from the source:
--   - reading: a demand bundle maximizes $u_i(\mathbf x_i)$ over bundles with $\sum_j p_jx_{ij}\le m_i$, bundles having $x_{ij}\in[0,1]$ (p.6) → the maximum is taken over all $y\ge 0$ with $\sum_j p_jy_j\le m_i$, without the box $y_j\le 1$; reason: with the box Lemma 4.3(a) fails (one agent, one item, $v=1$, $c=5$, $p=1/2$, $x=1$ would be an equilibrium in which the uncapped agent spends $1/2$); the paper computes the maximal utility as $\min\{c_i,m_i\alpha_i\}$ (proof of Lemma 3.5, p.14), the unboxed maximum; unit supply is enforced by $x_j\le e_j$
--   - reading: an allocation has $\sum_{i}x_{ij}=1$ for every good (p.6) → only $\sum_i x_{ij}\le e_j$ (Definition 2.1 (3)); reason: Definition 2.1 (3) and (5) force $x_j=e_j<1$ when $p_j>d_j$, and Proposition 3.1 (Property 1) has $x_{11}=1/2$
--   - encoding: $j$ is an MBB good of $i$ if $u_{ij}/p_j=\alpha_i$, with $\alpha_i=\infty$ for buyers interested in a zero-price good and $0/0=0$ (p.6) → $u_{ij}>0$ and $u_{ik}p_j\le u_{ij}p_k$ for all $k$; reason: no $\infty$ in $\mathbb R$; the same MBB goods for every buyer with some positive value; it differs only for a buyer whose values are all $0$, who then buys nothing (such a buyer violates money clearing, and in the goal makes every product $0$)
--   - encoding: modest supply $e_j=\min(1,d_j/p_j)$ (p.6) → $e_j=1$ when $p_j=0$, else $\min(1,d_j/p_j)$; reason: at $p_j=0$ the paper's $d_j/p_j$ is $+\infty$, while Lean's $d_j/0$ is $0$
--   - encoding: "we normalize $v'_{ij}=v_{ij}/\alpha_i$ and $c'_i=c_i/\alpha_i$" for $i\in B\setminus B_0$ and "assume that $v$ and $c$ fulfill these conditions directly" (p.24) → hypothesis `IsNormalized`: every buyer outside $B_0$ has MBB ratio $\alpha_i=\max_k u_{ik}/p_k=1$; reason: the paper's own convention; every normalized instance arises this way and the rescaling preserves money clearing, $v\le c$ and the equilibrium
--   - encoding: the procedure of §4.1.2 (pp.26–27) and Appendix B (pp.33–34), with arbitrary root choice and tie-breaks, run recursively → a relation `RoundingRun.IsValid` on the choices (an orientation of the allocation forest from root agents, a largest child per good, a greedy pick per agent), the kept child forced by the threshold, and the output defined from the recursion path; reason: the choices are exactly those the paper leaves free, and every valid run is covered; the recursion of Rounding (b) assigns the picked goods along the path to their parents and every other remaining good to its child agent
--   - reading: "each tree component $T$" after step (a) of rounding → the tree components of the forest after preprocessing that contain an agent, with $k_T$ the number of their goods that kept a child (the goods left after step (a)); reason: the goods assigned in step (a) are leaves, so removing them changes no component's agents; components without an agent are single unsold zero-price goods, which the procedure never roots
-- source:
--   Garg, Hoefer, Mehlhorn, Satiation in Fisher markets and approximation of Nash social welfare, arXiv:1707.04428v3 (31 Jul 2019), https://arxiv.org/abs/1707.04428v3, Lemma 4.5, p.27; procedure, pp.26–27

import Mathlib
import Definitions.Def_SatiationFisherNSW_NSWInstance
import Definitions.Def_SatiationFisherNSW_RoundingRun
open scoped Classical

namespace SatiationFisherNSW

/-- Lemma 4.5 (Garg, Hoefer, Mehlhorn, arXiv:1707.04428v3, p.27): after step (a) of rounding,
each tree component `T` has `k_T + 1` agents and `k_T` goods for some `k_T ≥ 0`. Suppose agent
`i` in `T` is assigned a good `j` with `p_j > 1` during step (a) of rounding. Then `i` spends all
its money on `j`, and `i` is the only agent that spends money on `j`. Moreover, the valuation of
`i` after rounding is `p_j`, and `B_c ∩ T = ∅`.

**Formalization Note** `T` ranges over the tree components of the forest after preprocessing
whose agents lie outside `B₀` (`IsPriceTree`); its goods at the end of Rounding (a) are
`remainingGoodsOf T` (the goods assigned in step (a) are leaves and do not affect the agents of
a component). "Assigned during step (a)" means: `j`'s parent agent is `i` and `j` kept no child.
"Spends all its money" is `p_j x_{ij} = m_i = 1`; "the only agent that spends money on `j`" is
`p_j x_{i'j} = 0` for `i' ≠ i`. The valuation after rounding is `v_i` of the output allocation,
and `B_c` is the set of capped buyers in `(x, p)`.
The standing assumptions of §4.1 are hypotheses: `v_{ij} ≤ c_i`
(p.23, "Henceforth"), the market of the instance (`u = v`, `m_i = d_j = 1`) is money clearing
(p.24, "for the remainder of this section"), `(x, p)` is a thrifty and modest equilibrium of it,
and the valuations are normalized according to `p` (MBB ratio `1` for every buyer outside `B₀`,
p.24).
A run of the procedure is any valid choice of roots, largest children and picks
(`RoundingRun.IsValid`); the statement holds for every run. -/
theorem lemma_4_5
    {B G : Type*} [Fintype B] [Fintype G] (I : NSWInstance B G)
    (hvc : ∀ i j, I.v i j ≤ I.c i) (hMC : I.market.IsMoneyClearing)
    (x : B → G → ℝ) (p : G → ℝ) (hEq : I.market.IsEquilibrium x p) (hN : I.IsNormalized p)
    (R : RoundingRun B G) (hR : R.IsValid I.market x p)
    (T : (R.ppGraph I.market x p).ConnectedComponent) (hT : R.IsPriceTree I.market x p T) :
    (R.agentsOf I.market x p T).card = (R.remainingGoodsOf I.market x p T).card + 1 ∧
    ∀ i ∈ R.agentsOf I.market x p T, ∀ j, R.parentAgent j = some i →
      R.keptChild I.market x p j = none → 1 < p j →
        p j * x i j = 1 ∧ (∀ i', i' ≠ i → p j * x i' j = 0) ∧
        I.val i (R.output I.market x p) = p j ∧
        ∀ a ∈ R.agentsOf I.market x p T, ¬ I.market.IsCapped x a := by sorry

end SatiationFisherNSW

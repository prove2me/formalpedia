-- Prove2me | Theorems.Thm_SatiationFisherNSW_lemma_4_4
-- name    : SatiationFisherNSW.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:45.696481+00:00
-- url     : https://prove2.me/theorems/c3a5b425-c454-4d88-bf7b-7a60dde3cedd
-- title:
--   Lemma 4.4 — preprocessing keeps at least half of each valuation
-- statement:
--   Under the standing assumptions of §4.1 (an instance with $v\le c$, a money-clearing Fisher market, a thrifty and modest equilibrium $(x,p)$, normalized valuations), consider any run of the rounding procedure and the trees of $(B\setminus B_0)\times(G\setminus G_0)$. After preprocessing:
--
--   1. the valuation of each root agent $r$ is at least $v_r(x)/2$;
--   2. the valuation of every other agent $i$ is at least $v_i(x)$;
--   3. if good $j$ has child agents and $p_j>1$, then $j$ keeps a child agent.
--
--   Here $v_i(x)=\min(c_i,\sum_jv_{ij}x_{ij})$, and the valuation after preprocessing is the same expression summed over the goods still adjacent to $i$.
--
--   **Formalization Note** "Root agents" after preprocessing are the original roots and the agents cut off from their parent good.
--
--   Differences from the source:
--   - reading: a demand bundle maximizes $u_i(\mathbf x_i)$ over bundles with $\sum_j p_jx_{ij}\le m_i$, bundles having $x_{ij}\in[0,1]$ (p.6) → the maximum is taken over all $y\ge 0$ with $\sum_j p_jy_j\le m_i$, without the box $y_j\le 1$; reason: with the box Lemma 4.3(a) fails (one agent, one item, $v=1$, $c=5$, $p=1/2$, $x=1$ would be an equilibrium in which the uncapped agent spends $1/2$); the paper computes the maximal utility as $\min\{c_i,m_i\alpha_i\}$ (proof of Lemma 3.5, p.14), the unboxed maximum; unit supply is enforced by $x_j\le e_j$
--   - reading: an allocation has $\sum_{i}x_{ij}=1$ for every good (p.6) → only $\sum_i x_{ij}\le e_j$ (Definition 2.1 (3)); reason: Definition 2.1 (3) and (5) force $x_j=e_j<1$ when $p_j>d_j$, and Proposition 3.1 (Property 1) has $x_{11}=1/2$
--   - encoding: $j$ is an MBB good of $i$ if $u_{ij}/p_j=\alpha_i$, with $\alpha_i=\infty$ for buyers interested in a zero-price good and $0/0=0$ (p.6) → $u_{ij}>0$ and $u_{ik}p_j\le u_{ij}p_k$ for all $k$; reason: no $\infty$ in $\mathbb R$; the same MBB goods for every buyer with some positive value; it differs only for a buyer whose values are all $0$, who then buys nothing (such a buyer violates money clearing, and in the goal makes every product $0$)
--   - encoding: modest supply $e_j=\min(1,d_j/p_j)$ (p.6) → $e_j=1$ when $p_j=0$, else $\min(1,d_j/p_j)$; reason: at $p_j=0$ the paper's $d_j/p_j$ is $+\infty$, while Lean's $d_j/0$ is $0$
--   - encoding: "we normalize $v'_{ij}=v_{ij}/\alpha_i$ and $c'_i=c_i/\alpha_i$" for $i\in B\setminus B_0$ and "assume that $v$ and $c$ fulfill these conditions directly" (p.24) → hypothesis `IsNormalized`: every buyer outside $B_0$ has MBB ratio $\alpha_i=\max_k u_{ik}/p_k=1$; reason: the paper's own convention; every normalized instance arises this way and the rescaling preserves money clearing, $v\le c$ and the equilibrium
--   - encoding: the procedure of §4.1.2 (pp.26–27) and Appendix B (pp.33–34), with arbitrary root choice and tie-breaks, run recursively → a relation `RoundingRun.IsValid` on the choices (an orientation of the allocation forest from root agents, a largest child per good, a greedy pick per agent), the kept child forced by the threshold, and the output defined from the recursion path; reason: the choices are exactly those the paper leaves free, and every valid run is covered; the recursion of Rounding (b) assigns the picked goods along the path to their parents and every other remaining good to its child agent
--   - encoding: "the valuation" after preprocessing → $\min(c_i,\sum_j u_{ij}x_{ij})$ over the goods adjacent to $i$ in the forest after preprocessing; reason: the fractional allocation restricted to the edges that are not cut
-- source:
--   Garg, Hoefer, Mehlhorn, Satiation in Fisher markets and approximation of Nash social welfare, arXiv:1707.04428v3 (31 Jul 2019), https://arxiv.org/abs/1707.04428v3, Lemma 4.4, p.27; procedure, pp.26–27

import Mathlib
import Definitions.Def_SatiationFisherNSW_NSWInstance
import Definitions.Def_SatiationFisherNSW_RoundingRun
open scoped Classical

namespace SatiationFisherNSW

/-- Lemma 4.4 (Garg, Hoefer, Mehlhorn, arXiv:1707.04428v3, p.27): after preprocessing, the
valuation of each root agent `r` is at least `v_r(x)/2`; for all other agents `i` the valuation
is at least `v_i(x)`; and if good `j` has child agents and `p_j > 1`, then `j` keeps a child
agent.

**Formalization Note** The lemma concerns the trees in `(B \ B₀) × (G \ G₀)` (p.26), so the
agents are those outside `B₀`. The valuation after preprocessing is
`min(c_i, Σ_j u_{ij} x_{ij})` over the goods still adjacent to `i` (`ppUtility`); `v_i(x)` is
`min(c_i, Σ_j u_{ij} x_{ij})` over all goods. A root after preprocessing is an original root or
an agent cut off from its parent good (`IsPPRoot`).
The standing assumptions of §4.1 are hypotheses: `v_{ij} ≤ c_i`
(p.23, "Henceforth"), the market of the instance (`u = v`, `m_i = d_j = 1`) is money clearing
(p.24, "for the remainder of this section"), `(x, p)` is a thrifty and modest equilibrium of it,
and the valuations are normalized according to `p` (MBB ratio `1` for every buyer outside `B₀`,
p.24).
A run of the procedure is any valid choice of roots, largest children and picks
(`RoundingRun.IsValid`); the statement holds for every run. -/
theorem lemma_4_4
    {B G : Type*} [Fintype B] [Fintype G] (I : NSWInstance B G)
    (hvc : ∀ i j, I.v i j ≤ I.c i) (hMC : I.market.IsMoneyClearing)
    (x : B → G → ℝ) (p : G → ℝ) (hEq : I.market.IsEquilibrium x p) (hN : I.IsNormalized p)
    (R : RoundingRun B G) (hR : R.IsValid I.market x p) :
    (∀ i, ¬ I.market.InB0 p i →
      (R.IsPPRoot I.market x p i → I.market.utility i (x i) / 2 ≤ R.ppUtility I.market x p i) ∧
      (¬ R.IsPPRoot I.market x p i → I.market.utility i (x i) ≤ R.ppUtility I.market x p i)) ∧
    (∀ j, 1 < p j → (∃ i, R.parentGood i = some j) →
      R.keptChild I.market x p j ≠ none) := by sorry

end SatiationFisherNSW

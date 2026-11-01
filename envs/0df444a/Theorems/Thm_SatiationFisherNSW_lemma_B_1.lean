-- Prove2me | Theorems.Thm_SatiationFisherNSW_lemma_B_1
-- name    : SatiationFisherNSW.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:26:00.998807+00:00
-- url     : https://prove2.me/theorems/8a23ab44-2e02-4cf7-a866-cab6ae8662fb
-- title:
--   Lemma B.1 — preprocessing on zero-price trees keeps half of each cap
-- statement:
--   Under the standing assumptions of §4.1, consider any run of the rounding procedure and the zero-price trees $T_0\subseteq B_0\times G_0$, on which the preprocessing keeps the largest child agent $i$ of a good $j$ only if $u_{ij}x_{ij}>c_i/2$. After preprocessing, the valuation of each root agent $r\in B_0$ is at least $c_r/2$, and the valuation of every other agent $i\in B_0$ is at least $c_i$.
--
--   The paper omits the proof as "almost completely identical" to that of Lemma 4.4.
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
--   Garg, Hoefer, Mehlhorn, Satiation in Fisher markets and approximation of Nash social welfare, arXiv:1707.04428v3 (31 Jul 2019), https://arxiv.org/abs/1707.04428v3, Lemma B.1, p.34; procedure, pp.33–34

import Mathlib
import Definitions.Def_SatiationFisherNSW_NSWInstance
import Definitions.Def_SatiationFisherNSW_RoundingRun
open scoped Classical

namespace SatiationFisherNSW

/-- Lemma B.1 (Garg, Hoefer, Mehlhorn, arXiv:1707.04428v3, p.34): for the zero-price trees
`T₀ ⊆ B₀ × G₀`, after preprocessing, the valuation of each root agent `r` is at least `c_r/2`;
for all other agents `i` the valuation is at least `c_i`.

**Formalization Note** The agents of zero-price trees are the agents of `B₀`. The valuation
after preprocessing is `min(c_i, Σ_j u_{ij} x_{ij})` over the goods still adjacent to `i`
(`ppUtility`). The caps of `B₀` are not rescaled by the normalization.
The standing assumptions of §4.1 are hypotheses: `v_{ij} ≤ c_i`
(p.23, "Henceforth"), the market of the instance (`u = v`, `m_i = d_j = 1`) is money clearing
(p.24, "for the remainder of this section"), `(x, p)` is a thrifty and modest equilibrium of it,
and the valuations are normalized according to `p` (MBB ratio `1` for every buyer outside `B₀`,
p.24).
A run of the procedure is any valid choice of roots, largest children and picks
(`RoundingRun.IsValid`); the statement holds for every run. -/
theorem lemma_B_1
    {B G : Type*} [Fintype B] [Fintype G] (I : NSWInstance B G)
    (hvc : ∀ i j, I.v i j ≤ I.c i) (hMC : I.market.IsMoneyClearing)
    (x : B → G → ℝ) (p : G → ℝ) (hEq : I.market.IsEquilibrium x p) (hN : I.IsNormalized p)
    (R : RoundingRun B G) (hR : R.IsValid I.market x p) :
    ∀ i, I.market.InB0 p i →
      (R.IsPPRoot I.market x p i → I.c i / 2 ≤ R.ppUtility I.market x p i) ∧
      (¬ R.IsPPRoot I.market x p i → I.c i ≤ R.ppUtility I.market x p i) := by sorry

end SatiationFisherNSW

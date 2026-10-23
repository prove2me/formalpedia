-- Prove2me | Theorems.Thm_SubsetShrink_Events_prob_F_weak
-- name    : SubsetShrink.Events.prob_F_weak
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-23T01:16:53.933044+00:00
-- url     : https://prove2.me/theorems/4fbf1b70-8cc3-430b-b2a5-4f06bd939240
-- title:
--   Theorem 1 (event $\mathcal F$) up to universal constants: sorted-sum and Lipschitz-deviation bounds for $\epsilon^\top Xu$
-- statement:
--   Work in the model of §3.1: $\epsilon\in\mathbb R^n$ has independent $N(0,\sigma^2)$ coordinates ($\sigma>0$), and the design $X\in\mathbb R^{n\times p}$, $p\ge1$, has columns of unit Euclidean norm. For $u\in\mathbb R^p$ write $u^\sharp_1\ge\dots\ge u^\sharp_p$ for the non-increasing rearrangement of $|u_1|,\dots,|u_p|$ and
--   $$N(u)=\sum_{j=1}^p u^\sharp_j\sqrt{\log(2p/j)} .$$
--
--   Then:
--
--   1. with probability at least $2/3$, simultaneously for all $u\in\mathbb R^p$,
--   $$\epsilon^\top Xu\le\sqrt{12}\,\sigma\,N(u);$$
--   2. for every $\delta_0\in(0,1)$, with probability at least $1-\delta_0$, simultaneously for all $u\in\mathbb R^p$,
--   $$\epsilon^\top Xu\le\sigma\max\Big(8N(u),\ 6\sqrt{\log(1/\delta_0)}\,\|Xu\|\Big).$$
--
--   Both events are measurable (they are closed sets of noise vectors).
--
--   This is the event $\mathcal F$ of Theorem 1 (p. 13), whose probability bound $P(\mathcal F)\ge1-\delta_0/2$ with the constant $4+\sqrt2$ the paper takes from Bellec, Lecué and Tsybakov (Theorem 4.1), stated here with other universal constants. The proof of Theorem 5 (B.13) only uses $\mathcal F$ up to universal constants ("$\lesssim$"). Part 1 is the analogue of BLT's Proposition E.2 (with $\sqrt{12}$ in place of $4$). Part 2 follows the route of BLT's Proposition E.3, using Gaussian concentration of Lipschitz functions about the **mean** rather than the median, which costs larger constants. Universal constants $8,6,\sqrt{12}$ and $2/3$ are explicit; nothing depends on $n,p,X,\sigma$.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 13, Theorem 1 (event F) and p. 38 (B.1), as used up to universal constants in the proof of Theorem 5 (B.13, pp. 49-51); argument after Bellec, Lecué & Tsybakov, Slope meets Lasso, arXiv:1605.08651, Appendix E, Propositions E.2-E.3 and Theorem 4.1, with mean (not median) Gaussian concentration

import Mathlib
import Definitions.Def_SubsetShrink_Events_Model

open MeasureTheory ProbabilityTheory

namespace SubsetShrink.Events

/-- Universal-constant form of the events of Theorem 1 used in the proof of Theorem 5:
(i) with probability at least `2/3`, `ϵ⊤Xu ≤ √12 σ ∑_j u♯_j √log(2p/j)` for all `u`;
(ii) for each `δ0 ∈ (0,1)`, with probability at least `1 − δ0`,
`ϵ⊤Xu ≤ σ max(8 ∑_j u♯_j √log(2p/j), 6 √log(1/δ0) ‖Xu‖)` for all `u`. -/
theorem prob_F_weak {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X) (hp : 1 ≤ p)
    (σ : ℝ) (hσ : 0 < σ) :
    (MeasurableSet {ε : Fin n → ℝ | ∀ u : Fin p → ℝ,
        dot ε (X.mulVec u) ≤ Real.sqrt 12 * σ * sortedSum u} ∧
      2 / 3 ≤ (noiseLaw n σ {ε : Fin n → ℝ | ∀ u : Fin p → ℝ,
        dot ε (X.mulVec u) ≤ Real.sqrt 12 * σ * sortedSum u}).toReal) ∧
    ∀ δ0 : ℝ, 0 < δ0 → δ0 < 1 →
      MeasurableSet {ε : Fin n → ℝ | ∀ u : Fin p → ℝ, dot ε (X.mulVec u) ≤
        σ * max (8 * sortedSum u) (6 * Real.sqrt (Real.log (1 / δ0)) * l2 (X.mulVec u))} ∧
      1 - δ0 ≤ (noiseLaw n σ {ε : Fin n → ℝ | ∀ u : Fin p → ℝ, dot ε (X.mulVec u) ≤
        σ * max (8 * sortedSum u) (6 * Real.sqrt (Real.log (1 / δ0)) * l2 (X.mulVec u))}).toReal := by sorry

end SubsetShrink.Events

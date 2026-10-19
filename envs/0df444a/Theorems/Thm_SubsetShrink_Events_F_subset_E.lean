-- Prove2me | Theorems.Thm_SubsetShrink_Events_F_subset_E
-- name    : SubsetShrink.Events.F_subset_E
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:40.902271+00:00
-- url     : https://prove2.me/theorems/4218f4d4-bd18-4289-80cf-8991e8d22843
-- title:
--   p. 38 — (28) and (27) yield the threshold bound, hence 𝓕 ⊆ 𝓔_s when δ₀ = s/(2ep)
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ have columns of unit Euclidean norm, let $\sigma>0$, $1\le s\le p$, and $\delta_0 = s/(2ep)$. Then for every $u\in B_0(s)$,
--   $$[4+\sqrt2]\,\sigma\max\Bigl(\sum_{j=1}^p u^\sharp_j\sqrt{\log(2p/j)},\ \sqrt{\log(1/\delta_0)}\,\|Xu\|\Bigr)\le[4+\sqrt2]\,\sigma\sqrt{s\log(2ep/s)}\,\|u\|,$$
--   and consequently the event $\mathcal F$ (with this $\delta_0$) is contained in the event $\mathcal E_s$.
--
--   Together with the bound $\mathbb P(\mathcal F)\ge1-\delta_0/2$ this gives $\mathbb P(\mathcal E_s)\ge1-s/(4ep)$, the first part of Theorem 1.
--
--   **Formalization Note** Events are sets of noise vectors $\epsilon\in\mathbb R^n$ (`F`, `E` of the definition file); $u^\sharp$ enters through `sortedSum`.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 38, proof of Theorem 1 (B.1), display after (28) and the sentence after it

import Mathlib
import Definitions.Def_SubsetShrink_Events_Model

open MeasureTheory ProbabilityTheory

namespace SubsetShrink.Events
theorem F_subset_E {n p s : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X)
    (σ : ℝ) (hσ : 0 < σ) (hs : 1 ≤ s) (hsp : s ≤ p) :
    (∀ u : Fin p → ℝ, l0 u ≤ s →
      (4 + Real.sqrt 2) * σ * max (sortedSum u)
          (Real.sqrt (Real.log (1 / ((s : ℝ) / (2 * Real.exp 1 * p)))) * l2 (X.mulVec u)) ≤
        (4 + Real.sqrt 2) * σ * Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) *
          l2 u) ∧
      F X σ ((s : ℝ) / (2 * Real.exp 1 * p)) ⊆ E X σ s := by sorry
end SubsetShrink.Events

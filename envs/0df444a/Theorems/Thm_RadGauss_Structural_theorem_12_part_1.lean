-- Prove2me | Theorems.Thm_RadGauss_Structural_theorem_12_part_1
-- name    : RadGauss.Structural.theorem_12_part_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T15:49:29.397597+00:00
-- url     : https://prove2.me/theorems/7557886f-fe76-4a5e-a5d3-99c700b9eab7
-- title:
--   Theorem 12, part 1 — if F ⊆ H then R_n(F) ≤ R_n(H)
-- statement:
--   **Theorem 12, part 1 (Bartlett–Mendelson 2002, p. 469).** Let $\mu$ be a probability measure on $\mathcal X$, $n\ge0$ an integer, and $R_n$ the Rademacher complexity of Definition 2 for an i.i.d. sample of size $n$ from $\mu$. If $F\subseteq H$ are classes of real functions on $\mathcal X$, then
--
--   $$
--   R_n(F)\le R_n(H).
--   $$
--
--   Monotonicity is the most basic structural property of the Rademacher complexity: enlarging a class can only increase its complexity. It is used, for instance, to show that the subadditivity bound of part 7 is tight.
--
--   **Formalization Note** No boundedness or measurability hypothesis is needed: complexities are $[0,\infty]$-valued and the comparison holds for every sample.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 469 (PDF p. 7), Theorem 12, part 1

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Structural

/-- **Theorem 12, part 1** (Bartlett–Mendelson, JMLR 3 (2002), p. 469): if `F ⊆ H` then
`R_n(F) ≤ R_n(H)`. -/
theorem theorem_12_part_1 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (F H : Set (X → ℝ)) (hFH : F ⊆ H) :
    RadGauss.RiskBound.rademacherComplexity μ n F ≤ RadGauss.RiskBound.rademacherComplexity μ n H := by sorry

end RadGauss.Structural

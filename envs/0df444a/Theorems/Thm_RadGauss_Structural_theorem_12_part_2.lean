-- Prove2me | Theorems.Thm_RadGauss_Structural_theorem_12_part_2
-- name    : RadGauss.Structural.theorem_12_part_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T15:49:40.810395+00:00
-- url     : https://prove2.me/theorems/6623db51-9fc3-4081-88aa-416e52cd540e
-- title:
--   Theorem 12, part 2 — R_n(F) = R_n(conv F) = R_n(absconv F)
-- statement:
--   **Theorem 12, part 2 (Bartlett–Mendelson 2002, p. 469).** Let $\mu$ be a probability measure on $\mathcal X$, $n\ge0$ an integer, and $R_n$ the Rademacher complexity of Definition 2. For a class $F$ of real functions on $\mathcal X$, let $\mathrm{conv}\,F$ be the class of convex combinations of functions from $F$, $-F=\{-f : f\in F\}$, and $\mathrm{absconv}\,F$ the class of convex combinations of functions from $F\cup -F$. Then
--
--   $$
--   R_n(F)=R_n(\mathrm{conv}\,F)=R_n(\mathrm{absconv}\,F).
--   $$
--
--   Passing to the convex hull, or to the symmetric convex hull, does not increase the Rademacher complexity. This is what makes Rademacher complexity bounds for voting methods (convex combinations of base classifiers) as good as those for the base class.
--
--   **Formalization Note** $\mathrm{conv}\,F$ is `convexHull ℝ F` in the vector space of functions $\mathcal X\to\mathbb R$, i.e. finite convex combinations (no closure), and $\mathrm{absconv}\,F$ is `convexHull ℝ (F ∪ -F)`. The chain is stated as the two equalities $R_n(F)=R_n(\mathrm{conv}\,F)$ and $R_n(\mathrm{conv}\,F)=R_n(\mathrm{absconv}\,F)$. No boundedness hypothesis: complexities are $[0,\infty]$-valued.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 469 (PDF p. 7), Theorem 12, part 2; notation conv, absconv from §2, p. 467 (PDF p. 5)

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Structural

/-- **Theorem 12, part 2** (Bartlett–Mendelson, JMLR 3 (2002), p. 469):
`R_n(F) = R_n(conv F) = R_n(absconv F)`, where `conv F` is the set of (finite) convex
combinations of functions of `F` and `absconv F = conv (F ∪ -F)`. -/
theorem theorem_12_part_2 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (F : Set (X → ℝ)) :
    RadGauss.RiskBound.rademacherComplexity μ n F = RadGauss.RiskBound.rademacherComplexity μ n (convexHull ℝ F) ∧
      RadGauss.RiskBound.rademacherComplexity μ n (convexHull ℝ F) =
        RadGauss.RiskBound.rademacherComplexity μ n (convexHull ℝ (F ∪ -F)) := by sorry

end RadGauss.Structural

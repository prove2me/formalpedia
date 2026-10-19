-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_unionHullSumCounterexample
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.unionHullSumCounterexample
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:16:31.189277+00:00
-- url     : https://prove2.me/theorems/0cd7340e-362b-4092-83da-b26d2efce826
-- title:
--   Remark 4: union/convex hull/Minkowski sum do not preserve µ-compactness
-- statement:
--   In $\ell^1(\mathbb N)$ let $A_1=\{x:x_i\ge0,\ \|x\|_1\le1\}$. Both $A_1$ and $-A_1$ are $\mu$-compact. Nevertheless,
--   $$A_1\cup(-A_1)\text{ is not }\mu\text{-compact},$$
--   and neither $\operatorname{co}(A_1\cup(-A_1))$ nor $A_1+(-A_1)$ is pointwise $\mu$-compact.
--
--   Symmetric two-atomic laws at the coordinate vectors have barycenter zero and escape compact sets.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 6, Remark 4: union/convex hull/Minkowski sum do not preserve µ-compactness

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section LpResults

/-- Remark 4, PDF pp.6,10: A_1 and −A_1 are µ-compact; their union fails
µ-compactness, and their convex hull and Minkowski sum even fail pointwise
µ-compactness. Symmetric Dirac laws of barycenter zero witness each failure. -/
theorem unionHullSumCounterexample :
    let A := positiveLpUnitPart 1
    let B := {x : lp (fun _ : ℕ => ℝ) 1 | -x ∈ A}
    MuCompact A ∧ MuCompact B ∧ ¬ MuCompact (A ∪ B) ∧
    ¬ PointwiseMuCompact (convexHull ℝ (A ∪ B)) ∧
    ¬ PointwiseMuCompact {z | ∃ x ∈ A, ∃ y ∈ B, z = x + y} := by sorry

end LpResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end

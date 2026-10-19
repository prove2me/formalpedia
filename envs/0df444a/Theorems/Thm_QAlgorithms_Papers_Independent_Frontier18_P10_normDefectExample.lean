-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_normDefectExample
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.normDefectExample
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:16:00.886199+00:00
-- url     : https://prove2.me/theorems/67ed41b7-794c-4f93-9d9e-f0a04fc5a87a
-- title:
--   Example 1: a concrete failure of closed-envelope interpolation
-- statement:
--   Fix a finite real $p>1$, let $A_p=\{x\in\ell^p(\mathbb N):x_i\ge0,\ \|x\|_p\le1\}$, and let $f(x)=1-\|x\|_p$. This is a bounded continuous real function and
--   $$\overline{\operatorname{co}}f(x)=0\quad(x\in A_p),\qquad
--   \overline{\operatorname{co}}f(0)\ne f(0).$$
--   Moreover, $A_p=\overline{\operatorname{co}}(\operatorname{extr}A_p)$ and its full barycenter map is open. There is no lower semicontinuous convex extension of $f|_{\operatorname{extr}A_p}$ to $A_p$, even allowing extended values.
--
--   This uses the explicit norm-defect witness instead of the source’s overly broad opening class of functions.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 13, Example 1: a concrete failure of closed-envelope interpolation

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

/-- Example 1, PDF p.13: the explicit f=1−norm has zero closed envelope,
fails equality at zero, and admits no lsc convex extension from extr A_p.
The extreme-generation and barycenter-openness clauses are retained. -/
theorem normDefectExample (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hfinite : p < ⊤) :
    let A := positiveLpUnitPart p
    let f := normDefect p
    BoundedContinuousOn A f ∧
    (∀ x ∈ A, closedConvexHullFunction A (fun y => (f y : EReal)) x = 0) ∧
    closedConvexHullFunction A (fun y => (f y : EReal)) 0 ≠ (f 0 : EReal) ∧
    closedConvexHull ℝ (A.extremePoints ℝ) = A ∧ BarycenterOpen A A ∧
    ¬ ∃ g : lp (fun _ : ℕ => ℝ) p → EReal,
      extendedConvexOn A g ∧ LowerSemicontinuous (fun x : A => g x) ∧
      (∀ x ∈ A.extremePoints ℝ, g x = (f x : EReal)) := by sorry

end LpResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_remark_4_20
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.remark_4_20
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:27:58.615994+00:00
-- url     : https://prove2.me/theorems/1677bc97-c18e-4758-8404-69f760ab63dc
-- title:
--   Remark 4.20
-- statement:
--   A closed densely defined operator admitting a D-calculus with the resolvent normalization and boundedness on every $\mathcal D_s$ must belong to $\operatorname{Sect}(\pi/2-)$. Likewise, admission of a bounded normalized $\mathcal H_\psi$ calculus forces
--
--   $$A\in\operatorname{Sect}(\theta)\quad\text{for some }0\le\theta<\psi.$$
--
--   These are converse characterizations; sectoriality and semigroup generation are conclusions.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 25, Remark 4.20

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Remark 4.20, arXiv:2202.03143v1, PDF page(s) 25. -/
theorem remark_4_20
:
    (∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X],
      ∀ A : DenseClosedGraphOperator X, ∀ F : AnalyticSymbol → X →L[ℂ] X,
      AlgebraMapOn hp F DUnion →
      (∀ lam ∈ hp, InverseAt A lam (F (resolventSymbol lam))) →
      (∀ s : ℝ, -1 < s → BoundedMapOn F (D s) (dSize s)) → SectorialBelow A) ∧
    (∀ psi : ℝ, 0 < psi → psi < Real.pi →
      ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X],
      ∀ A : DenseClosedGraphOperator X, ∀ F : AnalyticSymbol → X →L[ℂ] X,
      AlgebraMapOn (openSectorDomain psi) F (HardySobolevClass psi) → BoundedMapOn F (HardySobolevClass psi) (hSize psi) →
      (∀ lam ∈ openSectorDomain (Real.pi - psi), InverseAt A lam (F (resolventSymbol lam))) →
      ∃ theta : ℝ, 0 ≤ theta ∧ theta < psi ∧ SectorialAtAngle theta A) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end

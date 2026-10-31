-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_theorem_4_1
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.theorem_4_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:19:42.581976+00:00
-- url     : https://prove2.me/theorems/287a6c28-6bce-4811-9a86-93e3c39b22a9
-- title:
--   Theorem 4.1
-- statement:
--   There is an absolute $C>0$ such that every $A\in\operatorname{Sect}(\pi/2-)$ on any complex Banach space satisfies GSF with
--
--   $$\gamma_A\le CM_A(1+\log M_A),\qquad\|f(A)\|\le CM_A(1+\log M_A)\|f\|_{\mathcal B}.$$
--
--   Moreover $A$ has the B-calculus and its defining resolvent integral converges absolutely in operator norm, yielding $f(A)=f(\infty)I-(2/\pi)\int_0^\infty\alpha\int_{\mathbb R}f'(\alpha+i\beta)(\alpha-i\beta+A)^{-2}\,d\beta\,d\alpha$. This strengthens the weak construction for sectorial operators.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 18, Theorem 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Theorem 4.1, arXiv:2202.03143v1, PDF page(s) 18. -/
theorem theorem_4_1
:
    ∃ C : ℝ, 0 < C ∧
    ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X],
    ∀ A : DenseClosedGraphOperator X, SectorialBelow A →
      mSize A < ⊤ ∧ GSF A ∧
      gammaSize A ≤ ENNReal.ofReal
        (C * (mSize A).toReal * (Real.log (mSize A).toReal + 1)) ∧
      BCalculus A (bOperator A) ∧
      ∀ f, BesovClass f →
        ENNReal.ofReal ‖bOperator A f‖ ≤ ENNReal.ofReal
          (C * (mSize A).toReal * (Real.log (mSize A).toReal + 1)) * bSize f ∧
        AbsoluteOperatorDouble (besovOperatorIntegrand A f) ∧
        bOperator A f = infinityValue f • ContinuousLinearMap.id ℂ X -
          (2 / (Real.pi : ℂ)) •
            ∫ a, ∫ b, besovOperatorIntegrand A f a b ∂volume ∂positiveVolume := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end

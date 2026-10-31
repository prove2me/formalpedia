-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_theorem_3_13
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.theorem_3_13
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:16:22.287253+00:00
-- url     : https://prove2.me/theorems/82298ff1-dbcd-44c1-bb68-b5f80a07c10c
-- title:
--   Theorem 3.13
-- statement:
--   Let $A$ be a closed densely defined complex-linear operator on a complex Banach space satisfying the GSF assumptions. The concrete weak formula
--
--   $$\langle f(A)x,x^*\rangle=f(\infty)\langle x,x^*\rangle-\frac2\pi\int_0^\infty\!\alpha\int_{\mathbb R}\langle(\alpha-i\beta+A)^{-2}x,x^*\rangle f'(\alpha+i\beta)\,d\beta\,d\alpha$$
--
--   is represented by operators in $\mathcal L(X)$ for every $f\in\mathcal B$. These operators form a bounded algebra homomorphism $\Phi_A$ extending the Hille-Phillips calculus, with $\|\Phi_A\|\le\gamma_A$, where $\gamma_A$ is the least uniform constant in (3.14). This establishes existence of the B-calculus, including its range in $X$.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 13, Theorem 3.13

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Theorem 3.13, arXiv:2202.03143v1, PDF page(s) 1, 12, 13, 14. -/
theorem theorem_3_13
{X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
(A : DenseClosedGraphOperator X) (hA : GSF A) :
    gammaSize A < ⊤ ∧
    (∀ f, BesovClass f → RealizesB A f (bOperator A f)) ∧
    BCalculus A (bOperator A) ∧
    (∀ f, BesovClass f → ENNReal.ofReal ‖bOperator A f‖ ≤ gammaSize A * bSize f) ∧
    ∃ T : C0SemigroupData X, Generates T A ∧ HPCompatible T (bOperator A) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end

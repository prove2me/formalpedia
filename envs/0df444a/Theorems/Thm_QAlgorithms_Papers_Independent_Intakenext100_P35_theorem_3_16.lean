-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_theorem_3_16
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.theorem_3_16
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:17:35.540986+00:00
-- url     : https://prove2.me/theorems/5f12cfd6-ef42-4740-95e0-fb0fa7b86e30
-- title:
--   Theorem 3.16
-- statement:
--   Let $A$ satisfy GSF, $f\in\mathcal B$, and $\lambda\in\mathbb C$. Eigenvectors of $A$ and eigenfunctionals of its Banach transpose with eigenvalue $\lambda$ remain eigenvectors and eigenfunctionals of $f(A)$ with eigenvalue $f(\lambda)$. Unit approximate eigenvectors have the same property. Also $f(\sigma(A))\subset\sigma(f(A))$. If $A\in\operatorname{Sect}(\pi/2-)$, then
--
--   $$\sigma(f(A))\cup\{f(\infty)\}=f(\sigma(A))\cup\{f(\infty)\}.$$
--
--   All five clauses describe the spectral behavior of the B-calculus.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 14, Theorem 3.16

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Theorem 3.16, arXiv:2202.03143v1, PDF page(s) 14, 15. -/
theorem theorem_3_16
{X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
(A : DenseClosedGraphOperator X) (hA : GSF A) (f : AnalyticSymbol) (hf : BesovClass f) (lam : ℂ) :
    (∀ x : X, (x, lam • x) ∈ A.graph →
      bOperator A f x = extension hp f lam • x) ∧
    (∀ ell : X →L[ℂ] ℂ, TransposeEigen A lam ell →
      ∀ x : X, ell (bOperator A f x) = extension hp f lam * ell x) ∧
    (∀ xs ys : ℕ → X, (∀ n, (xs n, ys n) ∈ A.graph ∧ ‖xs n‖ = 1) →
      Tendsto (fun n => ‖ys n - lam • xs n‖) atTop (𝓝 0) →
      Tendsto (fun n => ‖bOperator A f (xs n) - extension hp f lam • xs n‖)
        atTop (𝓝 0)) ∧
    (lam ∈ operatorSpectrum A → extension hp f lam ∈ spectrum ℂ (bOperator A f)) ∧
    (SectorialBelow A → spectrum ℂ (bOperator A f) ∪ {infinityValue f} =
      (extension hp f) '' operatorSpectrum A ∪ {infinityValue f}) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end

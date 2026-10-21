-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P30_gaussian_traceRule
-- name    : QAlgorithms.Papers.Independent.Claimed50.P30.gaussian_traceRule
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:21:10.280686+00:00
-- url     : https://prove2.me/theorems/dd7d35fb-3897-4219-8c29-dce0449f92e1
-- title:
--   Gaussian trace pairing and characteristic-function integral
-- statement:
--   Let $n\ge1$ and let $\rho,\rho'$ be arbitrary Gaussian density operators on the completed $n$-mode oscillator Hilbert space, with displacements $u,u'\in\mathbb R^{2n}$ and physical covariance matrices $V,V'$. Quadratures are interleaved, their commutators are $2i\Omega$, and the vacuum covariance is $I$. Define
--   $$
--   D(\xi)=e^{i\hat x^T\xi},\qquad
--   \chi(\xi)=\operatorname{Tr}(\rho D(\xi)),\qquad
--   \chi'(\xi)=\operatorname{Tr}(\rho'D(\xi)).
--   $$
--   The function $\xi\mapsto\pi^{-n}\chi(\xi)\chi'(-\xi)$ is integrable for Lebesgue measure on $\mathbb R^{2n}$, the operator product $\rho\rho'$ is trace class, and
--   $$
--   \operatorname{Tr}(\rho\rho')
--   =\int_{\mathbb R^{2n}}\frac{d^{2n}\xi}{\pi^n}\,\chi(\xi)\chi'(-\xi)
--   =\frac{2^n}{\sqrt{\det(V+V')}}
--   \exp\!\left[-\frac12(u-u')^T(V+V')^{-1}(u-u')\right].
--   $$
--   This trace pairing connects actual Gaussian densities with their physical moments and is the overlap identity used in the proof of Theorem 2.
--
--   **Formalization Note** Integrability and convergence of the number-basis trace are conclusions. The integration measure uses $\pi^{-n}$, following (58), rather than the Wigner Fourier-transform normalization in (5).
-- source:
--   Computable bounds for the discrimination of Gaussian states, arXiv:0806.1625v2, PDF p. 5, Eq. (58), proof continuing from p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P30

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Mathlib supplies this C-star functional calculus as a theorem, not a global instance.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P30

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass IsPositive operatorTrace)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P04 (Covariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- Gaussian trace rule (58), arXiv:0806.1625v2, PDF pp.4--5.
The integration normalization is pi^n, not (2pi)^n. Integrability is a
conclusion, so the Bochner integral cannot silently take its default value. -/
theorem gaussian_traceRule {n : ℕ} (hn : 0 < n) (W : FockWeylSystem n)
    (A B : GaussianState n W) :
    let f := fun xi : PhaseVector n => ((Real.pi ^ n : ℝ) : ℂ)⁻¹ *
      modeWeylTrace W A.rho xi * modeWeylTrace W B.rho (-xi)
    let V := A.covariance + B.covariance
    let d := A.mean - B.mean
    Integrable f ∧ IsTraceClass (A.rho.comp B.rho) ∧
    TraceSummable (A.rho.comp B.rho) ∧
    trace (A.rho.comp B.rho) = ∫ xi, f xi ∧
    (∫ xi, f xi) =
      (((2 : ℝ) ^ n * Real.exp (-quadratic V⁻¹ d / 2) /
        Real.sqrt V.det : ℝ) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P30

end

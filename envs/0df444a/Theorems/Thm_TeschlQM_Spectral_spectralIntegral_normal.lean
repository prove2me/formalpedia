-- Prove2me | Theorems.Thm_TeschlQM_Spectral_spectralIntegral_normal
-- name    : TeschlQM.Spectral.spectralIntegral_normal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:29:15.962346+00:00
-- url     : https://prove2.me/theorems/2e541c6a-01b9-4a2d-862d-3b0d330672ac
-- title:
--   Theorem 3.2 — $P(f)$ is normal and $P(f)^* = P(f^*)$
-- statement:
--   Let $P$ be a projection-valued measure on a complex Hilbert space $\mathfrak H$ and let $f : \mathbb{R} \to \mathbb{C}$ be a Borel function. Then the operator
--   $$P(f) = \int_{\mathbb{R}} f(\lambda)\, dP(\lambda), \qquad \mathfrak D(P(f)) = \mathfrak D_f \qquad (3.28),$$
--   exists (it has domain $\mathfrak D_f$ and satisfies $\langle\psi, P(f)\psi\rangle = \int f\, d\mu_\psi$ on it), is normal, and satisfies
--   $$P(f)^* = P(f^*) \qquad (3.29),$$
--   where $f^*$ is the complex conjugate function.
--
--   In particular, for real-valued $f$ the operator $P(f)$ is self-adjoint; for $f(\lambda) = \lambda$ this is the self-adjoint operator $\int \lambda\, dP(\lambda)$ that the spectral theorem inverts.
--
--   **Formalization Note.** $P(f)$ is `spectralIntegral P f`, a `LinearPMap`; the first conjunct says it has the defining properties (domain $\mathfrak D_f$, quadratic form (3.17)). Normality (`IsNormalOperator`) includes density of $\mathfrak D_f$, without which the adjoint in (3.29) would be Mathlib's junk adjoint. (3.29) is an equality of `LinearPMap`s, domains included.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 92, Theorem 3.2

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Spectral_spectralIntegral
import Definitions.Def_TeschlQM_Spectral_IsNormalOperator

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral

/-- Teschl, p. 92, Theorem 3.2. For a projection-valued measure `P` and any Borel function `f`,
the operator `P(f) = ∫_ℝ f(λ) dP(λ)` with `𝔇(P(f)) = 𝔇_f` (3.28) is normal and satisfies
`P(f)* = P(f*)` (3.29). -/
theorem spectralIntegral_normal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P) (f : ℝ → ℂ) (hf : Measurable f) :
    IsSpectralIntegral P f (spectralIntegral P f) ∧
    IsNormalOperator (spectralIntegral P f) ∧
    (spectralIntegral P f).adjoint = spectralIntegral P (star f) := by sorry

end TeschlQM.Spectral

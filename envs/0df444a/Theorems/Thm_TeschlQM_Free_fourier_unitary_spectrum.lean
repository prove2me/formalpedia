-- Prove2me | Theorems.Thm_TeschlQM_Free_fourier_unitary_spectrum
-- name    : TeschlQM.Free.fourier_unitary_spectrum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T00:32:16.811195+00:00
-- url     : https://prove2.me/theorems/1461618e-5ff7-48f8-8956-01d173a6460d
-- title:
--   Theorem 7.5 — F extends to a unitary operator on L²(ℝⁿ) with σ(F) = {1, −1, i, −i}
-- statement:
--   Let $n \ge 1$. The Fourier transform $\hat f(p) = (2\pi)^{-n/2}\int e^{-ipx} f(x)\,d^nx$ extends to a unitary operator $\mathcal F : L^2(\mathbb R^n) \to L^2(\mathbb R^n)$: there is a surjective linear isometry of $L^2(\mathbb R^n)$ which agrees with the integral for every $f \in L^1(\mathbb R^n) \cap L^2(\mathbb R^n)$. Its spectrum is
--   $$\sigma(\mathcal F) = \{z \in \mathbb C \mid z^4 = 1\} = \{1, -1, i, -i\}.$$
--
--   The unitary Fourier transform is what makes the free Schrödinger operator unitarily equivalent to a multiplication operator.
--
--   **Formalization Note.** $U$ is a `LinearIsometryEquiv` of `Lp ℂ 2 volume`; it agrees almost everywhere with `fourier n ψ` whenever $\psi$ is integrable, and with `fourierL2 n ψ` (the $\hat\psi$ used elsewhere in this mission) for every $\psi$. Since $U$ is bounded, $\sigma(U)$ is Mathlib's Banach-algebra `spectrum ℂ` in the algebra of bounded operators, which is the book's spectrum for bounded operators. The hypothesis $n \ge 1$ is implicit in the book: for $n = 0$, $L^2(\mathbb R^0) = \mathbb C$ and $\mathcal F$ is the identity.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 164, Theorem 7.5

import Mathlib
import Definitions.Def_TeschlQM_Free_fourier

namespace TeschlQM.Free

open MeasureTheory

/-- Teschl, Theorem 7.5, p. 164: the Fourier transform `F` (Teschl's normalization (7.3)) extends to
a unitary operator `U` on `L²(ℝⁿ)`: `U` is a surjective linear isometry agreeing with the
integral (7.3) on `L¹ ∩ L²` (p. 164), and it is the transform `ψ ↦ ψ̂` (`fourierL2`) used in
this mission. Its spectrum is `σ(F) = {z ∈ ℂ | z⁴ = 1} = {1, -1, i, -i}` (7.11). `U` is bounded,
so its spectrum is Mathlib's Banach-algebra spectrum in `𝔏(L²(ℝⁿ))`. `n ≥ 1`: for `n = 0`,
`L²(ℝ⁰) = ℂ` and `F` is the identity. -/
theorem fourier_unitary_spectrum (n : ℕ) (hn : 0 < n) :
    ∃ U : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) ≃ₗᵢ[ℂ]
        Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
      (∀ ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
          Integrable (ψ : EuclideanSpace ℝ (Fin n) → ℂ) volume →
            (U ψ : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] fourier n ψ) ∧
        (∀ ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
          (U ψ : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] fourierL2 n ψ) ∧
        spectrum ℂ (U.toContinuousLinearEquiv.toContinuousLinearMap) =
          {1, -1, Complex.I, -Complex.I} := by sorry

end TeschlQM.Free

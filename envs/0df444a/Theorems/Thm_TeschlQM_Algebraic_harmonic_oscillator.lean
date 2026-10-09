-- Prove2me | Theorems.Thm_TeschlQM_Algebraic_harmonic_oscillator
-- name    : TeschlQM.Algebraic.harmonic_oscillator
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T03:01:01.460486+00:00
-- url     : https://prove2.me/theorems/6703d2e6-918a-402c-a50f-8c3fdc7827b9
-- title:
--   Theorem 8.5 — the harmonic oscillator: essential self-adjointness, Hermite eigenbasis, σ(H) = {(2n+3)ω}
-- statement:
--   Let $\omega > 0$ and let $H = -\Delta + \omega^2|x|^2$ be the harmonic oscillator in $L^2(\mathbb R^3)$ on the domain $\mathfrak D_\omega = \operatorname{span}\{x^\alpha e^{-\omega|x|^2/2} \mid \alpha \in \mathbb N_0^3\}$. Then such an operator exists, and it
--   - is **essentially self-adjoint** on $\mathfrak D_\omega$: its closure $\overline H$ is self-adjoint;
--   - has an orthonormal basis of eigenfunctions
--   $$\psi_{n_1,n_2,n_3}(x) = \psi_{n_1}(x_1)\psi_{n_2}(x_2)\psi_{n_3}(x_3), \qquad (n_1,n_2,n_3) \in \mathbb N_0^3,$$
--   with $\psi_n$ the Hermite functions $\psi_n(x) = (2^n n!)^{-1/2}(\omega/\pi)^{1/4} H_n(\sqrt\omega\,x) e^{-\omega x^2/2}$;
--   - has spectrum
--   $$\sigma(\overline H) = \{(2n + 3)\omega \mid n \in \mathbb N_0\}.$$
--
--   The harmonic oscillator is one of the few Schrödinger operators whose spectrum and eigenfunctions are known in closed form; it is the model for quantized vibrations and for the construction of Fock space.
--
--   **Formalization Note.** $L^2(\mathbb R^3)$ is `Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))`. $H$ is any `LinearPMap` with `IsHarmonicOscillator ω H` (domain $\mathfrak D_\omega$, action $-\Delta f + \omega^2|x|^2 f$ on representatives); the statement also asserts that such an $H$ exists, so it is not vacuous. Essential self-adjointness is `IsSelfAdjoint H.closure` (Mathlib's closure and adjoint of a `LinearPMap`). The basis is a `HilbertBasis (Fin 3 → ℕ) ℂ L²` whose $n$-th vector is a.e. equal to $\psi_{n_1,n_2,n_3}$ and is an eigenvector of $H$ itself. $\sigma$ is Teschl's spectrum of the closed operator $\overline H$ (bijectivity of $\overline H - z$ with bounded inverse), not Mathlib's Banach-algebra spectrum. **Deviation:** the domain is $\mathfrak D_\omega$ (Gaussian $e^{-\omega|x|^2/2}$) rather than (8.34)'s $e^{-|x|^2/2}$; the two coincide for $\omega = 1$, and $\mathfrak D_\omega$ is the space the book's proof uses (span$\{\psi_n\} = \mathfrak D$).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 179, Theorem 8.5

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Algebraic_gaussCore
import Definitions.Def_TeschlQM_Algebraic_IsHarmonicOscillator
import Definitions.Def_TeschlQM_Algebraic_hermiteFunction

namespace TeschlQM.Algebraic

open MeasureTheory

/-- Teschl, Theorem 8.5, p. 179. For `ω > 0`, the three-dimensional harmonic oscillator
`H = −Δ + ω²|x|²` on `𝔇_ω = span{x^α e^{−ω|x|²/2} | α ∈ ℕ₀³}` exists as an operator in
`L²(ℝ³)`, and every such `H`
* is essentially self-adjoint on `𝔇_ω` (its closure is self-adjoint),
* has an orthonormal basis of eigenfunctions `ψ_{n₁,n₂,n₃}(x) = ψ_{n₁}(x₁)ψ_{n₂}(x₂)ψ_{n₃}(x₃)`
  (8.43), with `ψₙ` the Hermite functions (8.41), and
* has spectrum `σ(H) = {(2n + 3)ω | n ∈ ℕ₀}` (8.44), the spectrum of its closure. -/
theorem harmonic_oscillator (ω : ℝ) (hω : 0 < ω) :
    (∃ H, IsHarmonicOscillator ω H) ∧
      ∀ H, IsHarmonicOscillator ω H →
        IsSelfAdjoint H.closure ∧
          (∃ b : HilbertBasis (Fin 3 → ℕ) ℂ
              (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))),
            ∀ n : Fin 3 → ℕ,
              ((b n : Lp ℂ 2 volume) : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume]
                  hermiteProduct ω n ∧
                ∃ h : b n ∈ H.domain, ∃ E : ℂ, H ⟨b n, h⟩ = E • b n) ∧
          TeschlQM.Shared.spectrum H.closure = {z : ℂ | ∃ n : ℕ, z = ((2 * n + 3 : ℝ) * ω : ℝ)} := by sorry

end TeschlQM.Algebraic

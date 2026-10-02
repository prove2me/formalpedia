-- Prove2me | Theorems.Thm_TeschlQM_Scattering_waveOp_unitary
-- name    : TeschlQM.Scattering.waveOp_unitary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T10:26:00.575613+00:00
-- url     : https://prove2.me/theorems/5b5116a3-e3fe-431e-9d47-eee004b211b8
-- title:
--   Lemma 12.1 — 𝔇(Ω±), Ran(Ω±) are closed and Ω± : 𝔇(Ω±) → Ran(Ω±) is unitary
-- statement:
--   Let $H_0 = \int\lambda\,dP_0(\lambda)$ and $H = \int\lambda\,dP(\lambda)$ be self-adjoint operators on a complex Hilbert space $\mathfrak H$, and let $\Omega_\pm\psi = \lim_{t\to\pm\infty}\mathrm e^{\mathrm itH}\mathrm e^{-\mathrm itH_0}\psi$ be the wave operators with domains $\mathfrak D(\Omega_\pm)$. Then $\mathfrak D(\Omega_\pm)$ and $\operatorname{Ran}(\Omega_\pm)$ are closed linear subspaces of $\mathfrak H$ and
--   $$\Omega_\pm : \mathfrak D(\Omega_\pm) \to \operatorname{Ran}(\Omega_\pm) \ \text{ is unitary.}$$
--   This is the basic structure of the wave operators: they are partial isometries from the asymptotic states onto the states that have an asymptotic state.
--
--   **Formalization Note.** The projection-valued measures $P_0$, $P$ are taken as data with `IsSpectralIntegral P₀ id H₀`, `IsSpectralIntegral P id H`. The sign is `s : ℤˣ` ($s = 1$ for $\Omega_+$, $s = -1$ for $\Omega_-$). The conclusion gives submodules $D$, $R$ with carriers $\mathfrak D(\Omega_\pm)$ and $\operatorname{Ran}(\Omega_\pm)$, both closed, and a linear isometric equivalence $D \simeq R$ that agrees with $\Omega_\pm$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 248, Lemma 12.1

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Shared_IsSpectralIntegral
import Definitions.Def_TeschlQM_Scattering_waveOperator

namespace TeschlQM.Scattering

/-- Teschl, p. 248, Lemma 12.1: `𝔇(Ω_±)` and `Ran(Ω_±)` are closed (linear subspaces) and
`Ω_± : 𝔇(Ω_±) → Ran(Ω_±)` is unitary. Here `H₀ = ∫ λ dP₀(λ)` and `H = ∫ λ dP(λ)` are
self-adjoint, with their projection-valued measures `P₀`, `P` taken as data; `s = ±1` is the
sign of `Ω_±`. -/
theorem waveOp_unitary {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ]
    (H₀ H : ℋ →ₗ.[ℂ] ℋ) (hH₀ : IsSelfAdjoint H₀) (hH : IsSelfAdjoint H)
    (P₀ P : Set ℝ → (ℋ →L[ℂ] ℋ))
    (hP₀ : TeschlQM.Shared.IsProjValuedMeasure P₀) (hP₀H₀ : TeschlQM.Shared.IsSpectralIntegral P₀ (fun x : ℝ => (x : ℂ)) H₀)
    (hP : TeschlQM.Shared.IsProjValuedMeasure P) (hPH : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) H)
    (s : ℤˣ) :
    ∃ D R : Submodule ℂ ℋ,
      (D : Set ℋ) = waveDomain P₀ P s ∧
      (R : Set ℋ) = waveOp P₀ P s '' waveDomain P₀ P s ∧
      IsClosed (D : Set ℋ) ∧ IsClosed (R : Set ℋ) ∧
      ∃ W : D ≃ₗᵢ[ℂ] R, ∀ ψ : D, (W ψ : ℋ) = waveOp P₀ P s (ψ : ℋ) := by sorry

end TeschlQM.Scattering

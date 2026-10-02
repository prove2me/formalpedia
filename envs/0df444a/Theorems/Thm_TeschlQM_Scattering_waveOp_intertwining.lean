-- Prove2me | Theorems.Thm_TeschlQM_Scattering_waveOp_intertwining
-- name    : TeschlQM.Scattering.waveOp_intertwining
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T10:29:24.763766+00:00
-- url     : https://prove2.me/theorems/925cb766-0613-442f-9e0d-75dd80e7fbe7
-- title:
--   Theorem 12.2 — reducing subspaces and the intertwining property Ω±H₀ = HΩ±
-- statement:
--   Let $H_0 = \int\lambda\,dP_0$ and $H = \int\lambda\,dP$ be self-adjoint and $\Omega_\pm$ the wave operators. Then $\mathfrak D(\Omega_\pm)$ reduces $H_0$, $\operatorname{Ran}(\Omega_\pm)$ reduces $H$, and the restricted operators are unitarily equivalent through $\Omega_\pm$:
--   $$\Omega_\pm H_0\psi = H\Omega_\pm\psi, \qquad \psi \in \mathfrak D(\Omega_\pm) \cap \mathfrak D(H_0). \tag{12.8}$$
--   Unitary equivalence includes the domains: $\Omega_\pm$ maps $\mathfrak D(\Omega_\pm) \cap \mathfrak D(H_0)$ onto $\operatorname{Ran}(\Omega_\pm) \cap \mathfrak D(H)$. This intertwining property is what makes the wave operators compatible with the energy: $H$ restricted to $\operatorname{Ran}(\Omega_\pm)$ is a copy of $H_0$ restricted to $\mathfrak D(\Omega_\pm)$.
--
--   **Formalization Note.** $P_0$, $P$ are data as in Lemma 12.1; sign `s : ℤˣ`. (12.8) is stated with its implicit memberships: for $\psi \in \mathfrak D(\Omega_\pm) \cap \mathfrak D(H_0)$, $H_0\psi \in \mathfrak D(\Omega_\pm)$, $\Omega_\pm\psi \in \mathfrak D(H)$, and $\Omega_\pm(H_0\psi) = H(\Omega_\pm\psi)$. "Reduces" is Teschl's $P_1A \subseteq AP_1$ (p. 80).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 248, Theorem 12.2, Eq. (12.8)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Shared_IsSpectralIntegral
import Definitions.Def_TeschlQM_Scattering_waveOperator
import Definitions.Def_TeschlQM_Scattering_Reduces

namespace TeschlQM.Scattering

/-- Teschl, p. 248, Theorem 12.2: `𝔇(Ω_±)` reduces `H₀` and `Ran(Ω_±)` reduces `H`, and the
restricted operators are unitarily equivalent through `Ω_±`: `Ω_±` maps `𝔇(Ω_±) ∩ 𝔇(H₀)` onto
`Ran(Ω_±) ∩ 𝔇(H)`, and `Ω_± H₀ ψ = H Ω_± ψ` for `ψ ∈ 𝔇(Ω_±) ∩ 𝔇(H₀)` (12.8) (in particular
`H₀ψ ∈ 𝔇(Ω_±)` and `Ω_±ψ ∈ 𝔇(H)`). `H₀ = ∫ λ dP₀`, `H = ∫ λ dP`, with `P₀`, `P` as data. -/
theorem waveOp_intertwining {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ]
    (H₀ H : ℋ →ₗ.[ℂ] ℋ) (hH₀ : IsSelfAdjoint H₀) (hH : IsSelfAdjoint H)
    (P₀ P : Set ℝ → (ℋ →L[ℂ] ℋ))
    (hP₀ : TeschlQM.Shared.IsProjValuedMeasure P₀) (hP₀H₀ : TeschlQM.Shared.IsSpectralIntegral P₀ (fun x : ℝ => (x : ℂ)) H₀)
    (hP : TeschlQM.Shared.IsProjValuedMeasure P) (hPH : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) H)
    (s : ℤˣ) :
    Reduces (waveDomain P₀ P s) H₀ ∧
    Reduces (waveOp P₀ P s '' waveDomain P₀ P s) H ∧
    waveOp P₀ P s '' (waveDomain P₀ P s ∩ (H₀.domain : Set ℋ)) =
      (waveOp P₀ P s '' waveDomain P₀ P s) ∩ (H.domain : Set ℋ) ∧
    ∀ ψ : H₀.domain, (ψ : ℋ) ∈ waveDomain P₀ P s →
      H₀ ψ ∈ waveDomain P₀ P s ∧
      ∃ h : waveOp P₀ P s (ψ : ℋ) ∈ H.domain,
        waveOp P₀ P s (H₀ ψ) = H ⟨waveOp P₀ P s (ψ : ℋ), h⟩ := by sorry

end TeschlQM.Scattering

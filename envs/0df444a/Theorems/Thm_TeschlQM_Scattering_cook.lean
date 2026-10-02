-- Prove2me | Theorems.Thm_TeschlQM_Scattering_cook
-- name    : TeschlQM.Scattering.cook
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T10:32:25.991223+00:00
-- url     : https://prove2.me/theorems/8fdefdbf-5d6a-4f8a-8af9-82ee203bc252
-- title:
--   Lemma 12.3 (Cook) — integrability of ‖(H − H₀)e^{∓itH₀}ψ‖ gives ψ ∈ 𝔇(Ω±)
-- statement:
--   Let $H_0 = \int\lambda\,dP_0$ and $H = \int\lambda\,dP$ be self-adjoint with $\mathfrak D(H) \subseteq \mathfrak D(H_0)$, and let $\psi \in \mathfrak D(H_0)$. If
--   $$\int_0^\infty \|(H - H_0)\exp(\mp\mathrm itH_0)\psi\|\,dt < \infty, \tag{12.11}$$
--   then $\psi \in \mathfrak D(\Omega_\pm)$, respectively, and
--   $$\|(\Omega_\pm - \mathbb I)\psi\| \le \int_0^\infty \|(H - H_0)\exp(\mp\mathrm itH_0)\psi\|\,dt. \tag{12.12}$$
--   Cook's criterion turns the existence of the wave operators into a decay estimate for the free evolution seen through the perturbation $H - H_0$.
--
--   **Formalization Note.** The integrand of (12.11) presupposes that $(H - H_0)\exp(\mp\mathrm itH_0)\psi$ is defined, i.e. $\exp(\mp\mathrm itH_0)\psi \in \mathfrak D(H)$ for $t \ge 0$; this is stated as a hypothesis (it is automatic when $\mathfrak D(H) = \mathfrak D(H_0)$, as for $H = H_0 + V$). $\exp(\mp\mathrm itH_0) = $ `timeEvolution P₀ (s t)` with sign `s : ℤˣ`. "$\int_0^\infty \ldots < \infty$" is integrability on $(0,\infty)$ (`IntegrableOn`), and the right-hand side of (12.12) is the Bochner integral. $(H - H_0)\varphi$ is written `applyExt H φ − applyExt H₀ φ`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 249, Lemma 12.3, Eqs. (12.11)–(12.12)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Shared_IsSpectralIntegral
import Definitions.Def_TeschlQM_Scattering_waveOperator
import Definitions.Def_TeschlQM_Scattering_applyExt

open MeasureTheory

namespace TeschlQM.Scattering

/-- Teschl, p. 249, Lemma 12.3 (Cook): suppose `𝔇(H) ⊆ 𝔇(H₀)`, let `ψ ∈ 𝔇(H₀)` and
`s = ±1`. If `(H − H₀) exp(∓itH₀)ψ` is defined for `t ≥ 0` (i.e. `exp(∓itH₀)ψ ∈ 𝔇(H)`, which the
integrand of (12.11) presupposes) and `∫₀^∞ ‖(H − H₀) exp(∓itH₀)ψ‖ dt < ∞` (12.11), then
`ψ ∈ 𝔇(Ω_±)` and `‖(Ω_± − 𝕀)ψ‖ ≤ ∫₀^∞ ‖(H − H₀) exp(∓itH₀)ψ‖ dt` (12.12).
`exp(∓itH₀) = timeEvolution P₀ (s t)`; finiteness of the integral is integrability on
`(0, ∞)`. `H₀ = ∫ λ dP₀`, `H = ∫ λ dP`, with `P₀`, `P` as data. -/
theorem cook {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (H₀ H : ℋ →ₗ.[ℂ] ℋ) (hH₀ : IsSelfAdjoint H₀) (hH : IsSelfAdjoint H)
    (P₀ P : Set ℝ → (ℋ →L[ℂ] ℋ))
    (hP₀ : TeschlQM.Shared.IsProjValuedMeasure P₀) (hP₀H₀ : TeschlQM.Shared.IsSpectralIntegral P₀ (fun x : ℝ => (x : ℂ)) H₀)
    (hP : TeschlQM.Shared.IsProjValuedMeasure P) (hPH : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) H)
    (hdom : H.domain ≤ H₀.domain) (s : ℤˣ) (ψ : ℋ) (hψ : ψ ∈ H₀.domain)
    (hdef : ∀ t : ℝ, 0 ≤ t → TeschlQM.Shared.timeEvolution P₀ (((s : ℤ) : ℝ) * t) ψ ∈ H.domain)
    (hint : IntegrableOn (fun t : ℝ =>
        ‖applyExt H (TeschlQM.Shared.timeEvolution P₀ (((s : ℤ) : ℝ) * t) ψ) -
          applyExt H₀ (TeschlQM.Shared.timeEvolution P₀ (((s : ℤ) : ℝ) * t) ψ)‖) (Set.Ioi 0)) :
    ψ ∈ waveDomain P₀ P s ∧
    ‖waveOp P₀ P s ψ - ψ‖ ≤
      ∫ t in Set.Ioi (0 : ℝ),
        ‖applyExt H (TeschlQM.Shared.timeEvolution P₀ (((s : ℤ) : ℝ) * t) ψ) -
          applyExt H₀ (TeschlQM.Shared.timeEvolution P₀ (((s : ℤ) : ℝ) * t) ψ)‖ := by sorry

end TeschlQM.Scattering

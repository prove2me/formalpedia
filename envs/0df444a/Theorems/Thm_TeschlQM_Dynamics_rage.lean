-- Prove2me | Theorems.Thm_TeschlQM_Dynamics_rage
-- name    : TeschlQM.Dynamics.rage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T07:08:22.887295+00:00
-- url     : https://prove2.me/theorems/35eaff73-928c-4501-ad0b-784580061f1d
-- title:
--   Theorem 5.7 (RAGE) — dynamical characterization of ℌ_c and ℌ_pp
-- statement:
--   Let $A$ be self-adjoint in a complex Hilbert space $\mathfrak H$. Suppose $K_n \in \mathfrak L(\mathfrak H)$ is a sequence of relatively compact operators which converges strongly to the identity. Then
--   $$\mathfrak H_c = \Big\{\psi \in \mathfrak H \;\Big|\; \lim_{n\to\infty} \lim_{T\to\infty} \frac1T \int_0^T \|K_n \mathrm e^{-\mathrm itA}\psi\|\, dt = 0\Big\},$$
--   $$\mathfrak H_{pp} = \Big\{\psi \in \mathfrak H \;\Big|\; \lim_{n\to\infty} \sup_{t\ge 0} \|(\mathbb I - K_n)\mathrm e^{-\mathrm itA}\psi\| = 0\Big\}.$$
--
--   Here $\mathfrak H_c = \mathfrak H_{ac} \oplus \mathfrak H_{sc}$ and $\mathfrak H_{pp}$ are the spectral subspaces defined from the spectral measures $\mu_\psi$. The theorem (Ruelle, Amrein–Georgescu, Enß) says that continuous-spectrum states escape, on time average, from every "compact region" $K_n$, while pure-point states stay uniformly localized for all times.
--
--   **Formalization Note.** $\mathrm e^{-\mathrm itA}$ and the spectral subspaces are defined from a projection-valued measure $P$ taken as data with $A = \int\lambda\, dP(\lambda)$; $\mathfrak H_c$ and $\mathfrak H_{pp}$ are defined from the spectral measures, never from the dynamical conditions. The iterated limit means: for each $n$ the limit $L_n$ as $T \to \infty$ exists, and $L_n \to 0$. The supremum over $t \ge 0$ is taken in $[0,\infty]$ (extended nonnegative reals), so it is never truncated. Separability of $\mathfrak H$ is not assumed.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 129, Theorem 5.7, Eq. (5.14)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Shared_IsSpectralIntegral
import Definitions.Def_TeschlQM_Shared_timeEvolution
import Definitions.Def_TeschlQM_Dynamics_spectralSubspaces
import Definitions.Def_TeschlQM_Dynamics_IsRelativelyCompact

open Filter Topology
open scoped ENNReal

namespace TeschlQM.Dynamics

/-- Teschl, Theorem 5.7 (RAGE), p. 129, (5.14): let `A = ∫ λ dP(λ)` be self-adjoint and let
`K_n ∈ 𝔏(ℌ)` be relatively compact operators converging strongly to `𝕀`. Then
`ℌ_c = {ψ | lim_{n→∞} lim_{T→∞} (1/T) ∫₀ᵀ ‖K_n e^{−itA} ψ‖ dt = 0}` (for each `n` the inner limit
exists, and these limits tend to `0`) and
`ℌ_pp = {ψ | lim_{n→∞} sup_{t≥0} ‖(𝕀 − K_n) e^{−itA} ψ‖ = 0}` (the supremum taken in `[0, ∞]`).
`ℌ_c = ℌ_ac ⊕ ℌ_sc` and `ℌ_pp` are defined from the spectral measures `μ_ψ` (3.83). -/
theorem rage {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) A)
    (K : ℕ → H →L[ℂ] H) (hK : ∀ n, IsRelativelyCompact ((K n : H →ₗ[ℂ] H).toPMap ⊤) A)
    (hKI : ∀ ψ : H, Tendsto (fun n => K n ψ) atTop (𝓝 ψ)) :
    hc P = {ψ : H | ∃ L : ℕ → ℝ,
      (∀ n, Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, ‖K n (TeschlQM.Shared.timeEvolution P t ψ)‖)
        atTop (𝓝 (L n))) ∧ Tendsto L atTop (𝓝 0)} ∧
    hpp P = {ψ : H | Tendsto (fun n : ℕ => ⨆ t : Set.Ici (0 : ℝ),
      ‖TeschlQM.Shared.timeEvolution P t ψ - K n (TeschlQM.Shared.timeEvolution P t ψ)‖ₑ) atTop (𝓝 0)} := by sorry

end TeschlQM.Dynamics

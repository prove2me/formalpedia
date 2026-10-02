-- Prove2me | Theorems.Thm_TeschlQM_Dynamics_heisenberg_cesaro_limit
-- name    : TeschlQM.Dynamics.heisenberg_cesaro_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T07:16:28.379408+00:00
-- url     : https://prove2.me/theorems/9a98cd69-aae0-4948-9f96-8d1e1d8964c2
-- title:
--   Theorem 5.8 — time average of e^{itA}Ke^{−itA} is Σ_{λ∈σ_p(A)} P_A({λ})KP_A({λ})
-- statement:
--   Suppose $A$ is self-adjoint and $K$ is relatively compact with respect to $A$. Then
--   $$\lim_{T\to\infty} \frac1T \int_0^T \mathrm e^{\mathrm itA} K \mathrm e^{-\mathrm itA}\psi\, dt = \sum_{\lambda\in\sigma_p(A)} P_A(\{\lambda\}) K P_A(\{\lambda\})\psi, \qquad \psi \in \mathfrak D(A).$$
--   If $K$ is in addition bounded, the result holds for any $\psi \in \mathfrak H$.
--
--   In the Heisenberg picture $K(t) = \mathrm e^{\mathrm itA}K\mathrm e^{-\mathrm itA}$, the time average of a relatively compact observable only retains its diagonal blocks with respect to the eigenspaces of $A$.
--
--   **Formalization Note.** $P_A = P$ is a projection-valued measure taken as data with $A = \int\lambda\, dP(\lambda)$, and $\mathrm e^{\pm\mathrm itA}$ are defined from it. The integral is the Bochner integral of the $\mathfrak H$-valued function $t \mapsto \mathrm e^{\mathrm itA} K \mathrm e^{-\mathrm itA}\psi$. The sum over $\sigma_p(A)$ is an unconditional sum in $\mathfrak H$, whose convergence is part of the conclusion. $K$ is applied through `applyExt`, which agrees with $K$ on $\mathfrak D(A) \subseteq \mathfrak D(K)$ (eigenvectors lie in $\mathfrak D(A)$). "$K$ bounded" means an everywhere defined $K_b \in \mathfrak L(\mathfrak H)$ with `K_b.toPMap ⊤ = K`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 130, Theorem 5.8, Eq. (5.18)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Shared_IsSpectralIntegral
import Definitions.Def_TeschlQM_Shared_timeEvolution
import Definitions.Def_TeschlQM_Dynamics_IsRelativelyCompact
import Definitions.Def_TeschlQM_Dynamics_pointSpectrum

open Filter Topology

namespace TeschlQM.Dynamics

/-- Teschl, Theorem 5.8, p. 130, (5.18): let `A = ∫ λ dP(λ)` be self-adjoint (so `P_A = P`) and
`K` relatively compact with respect to `A`. Then for `ψ ∈ 𝔇(A)`
`lim_{T→∞} (1/T) ∫₀ᵀ e^{itA} K e^{−itA} ψ dt = ∑_{λ∈σ_p(A)} P_A({λ}) K P_A({λ}) ψ`,
the sum over the eigenvalues of `A` converging (unconditionally) in `ℌ`. If `K` is in addition
bounded (an everywhere defined `K_b ∈ 𝔏(ℌ)`), the same holds for every `ψ ∈ ℌ`. The integral is
the Bochner integral of `t ↦ e^{itA} K e^{−itA} ψ`, `e^{itA} = U(−t)`. -/
theorem heisenberg_cesaro_limit {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) A)
    (K : H →ₗ.[ℂ] H) (hK : IsRelativelyCompact K A) :
    (∀ ψ ∈ A.domain,
      Summable (fun x : pointSpectrum A => P {(x : ℝ)} (applyExt K (P {(x : ℝ)} ψ))) ∧
      Tendsto (fun T : ℝ => (1 / T) • ∫ t in (0 : ℝ)..T,
          TeschlQM.Shared.timeEvolution P (-t) (applyExt K (TeschlQM.Shared.timeEvolution P t ψ))) atTop
        (𝓝 (∑' x : pointSpectrum A, P {(x : ℝ)} (applyExt K (P {(x : ℝ)} ψ))))) ∧
    ∀ Kb : H →L[ℂ] H, (Kb : H →ₗ[ℂ] H).toPMap ⊤ = K → ∀ ψ : H,
      Summable (fun x : pointSpectrum A => P {(x : ℝ)} (Kb (P {(x : ℝ)} ψ))) ∧
      Tendsto (fun T : ℝ => (1 / T) • ∫ t in (0 : ℝ)..T,
          TeschlQM.Shared.timeEvolution P (-t) (Kb (TeschlQM.Shared.timeEvolution P t ψ))) atTop
        (𝓝 (∑' x : pointSpectrum A, P {(x : ℝ)} (Kb (P {(x : ℝ)} ψ)))) := by sorry

end TeschlQM.Dynamics

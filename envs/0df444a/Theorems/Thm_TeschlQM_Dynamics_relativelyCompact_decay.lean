-- Prove2me | Theorems.Thm_TeschlQM_Dynamics_relativelyCompact_decay
-- name    : TeschlQM.Dynamics.relativelyCompact_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T07:03:39.983274+00:00
-- url     : https://prove2.me/theorems/53f18ef5-abb9-44c5-ba3d-dd377c415bca
-- title:
--   Theorem 5.6 — relatively compact K kills e^{−itA}P^cψ on average and e^{−itA}P^{ac}ψ as t → ∞
-- statement:
--   Let $A$ be self-adjoint and suppose $K$ is relatively compact with respect to $A$. Let $P^c$ and $P^{ac}$ be the orthogonal projections onto $\mathfrak H_c$ and $\mathfrak H_{ac}$. Then
--   $$\lim_{T\to\infty} \frac1T \int_0^T \|K\mathrm e^{-\mathrm itA}P^c\psi\|^2\, dt = 0 \qquad\text{and}\qquad \lim_{t\to\infty} \|K\mathrm e^{-\mathrm itA}P^{ac}\psi\| = 0$$
--   for every $\psi \in \mathfrak D(A)$. If, in addition, $K$ is bounded, then the result holds for any $\psi \in \mathfrak H$.
--
--   States in the continuous subspace leave, on average, every region that a relatively compact operator can "see"; absolutely continuous states leave it for good.
--
--   **Formalization Note.** $\mathrm e^{-\mathrm itA}$ and the spectral subspaces come from a projection-valued measure $P$ taken as data with $A = \int\lambda\, dP$. $K$ is a `LinearPMap`; for $\psi \in \mathfrak D(A)$ the vectors $\mathrm e^{-\mathrm itA}P^{c}\psi$, $\mathrm e^{-\mathrm itA}P^{ac}\psi$ lie in $\mathfrak D(A) \subseteq \mathfrak D(K)$, and $K$ is applied through `applyExt`, which agrees with $K$ there. "$K$ is bounded" means $K$ is an everywhere defined bounded operator $K_b \in \mathfrak L(\mathfrak H)$ (`K_b.toPMap ⊤ = K`).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 128, Theorem 5.6, Eq. (5.13)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Shared_IsSpectralIntegral
import Definitions.Def_TeschlQM_Shared_timeEvolution
import Definitions.Def_TeschlQM_Dynamics_spectralSubspaces
import Definitions.Def_TeschlQM_Dynamics_IsRelativelyCompact

open Filter Topology

namespace TeschlQM.Dynamics

/-- Teschl, Theorem 5.6, p. 128, (5.13): let `A = ∫ λ dP(λ)` be self-adjoint and `K` relatively
compact with respect to `A`. Then
`lim_{T→∞} (1/T) ∫₀ᵀ ‖K e^{−itA} P^c ψ‖² dt = 0` and `lim_{t→∞} ‖K e^{−itA} P^{ac} ψ‖ = 0`
for every `ψ ∈ 𝔇(A)` (the vectors `e^{−itA} P^c ψ`, `e^{−itA} P^{ac} ψ` lie in `𝔇(A) ⊆ 𝔇(K)`).
If, in addition, `K` is bounded (`K` is an everywhere defined `K_b ∈ 𝔏(ℌ)`), the same holds for
every `ψ ∈ ℌ`. `P^c`, `P^{ac}` are the orthogonal projections onto `ℌ_c`, `ℌ_ac`. -/
theorem relativelyCompact_decay {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) A)
    (K : H →ₗ.[ℂ] H) (hK : IsRelativelyCompact K A) :
    (∀ ψ ∈ A.domain,
      Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
          ‖applyExt K (TeschlQM.Shared.timeEvolution P t (orthProj (hc P) ψ))‖ ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => ‖applyExt K (TeschlQM.Shared.timeEvolution P t (orthProj (hac P) ψ))‖) atTop
        (𝓝 0)) ∧
    ∀ Kb : H →L[ℂ] H, (Kb : H →ₗ[ℂ] H).toPMap ⊤ = K → ∀ ψ : H,
      Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
          ‖Kb (TeschlQM.Shared.timeEvolution P t (orthProj (hc P) ψ))‖ ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => ‖Kb (TeschlQM.Shared.timeEvolution P t (orthProj (hac P) ψ))‖) atTop
        (𝓝 0) := by sorry

end TeschlQM.Dynamics

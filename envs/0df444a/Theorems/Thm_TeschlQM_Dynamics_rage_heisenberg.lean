-- Prove2me | Theorems.Thm_TeschlQM_Dynamics_rage_heisenberg
-- name    : TeschlQM.Dynamics.rage_heisenberg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T07:20:35.013553+00:00
-- url     : https://prove2.me/theorems/ac4051f2-99eb-437f-96c4-7d30aca39a91
-- title:
--   Corollary 5.9 — iterated time averages of e^{itA}K_ne^{−itA} give P^{pp} and P^c
-- statement:
--   Under the same assumptions as in the RAGE theorem ($A$ self-adjoint, $K_n \in \mathfrak L(\mathfrak H)$ relatively compact with $K_n \to \mathbb I$ strongly) we have, for every $\psi \in \mathfrak H$,
--   $$\lim_{n\to\infty}\lim_{T\to\infty} \frac1T \int_0^T \mathrm e^{\mathrm itA} K_n \mathrm e^{-\mathrm itA}\psi\, dt = P^{pp}\psi,$$
--   respectively,
--   $$\lim_{n\to\infty}\lim_{T\to\infty} \frac1T \int_0^T \mathrm e^{\mathrm itA} (\mathbb I - K_n) \mathrm e^{-\mathrm itA}\psi\, dt = P^{c}\psi,$$
--   where $P^{pp}$ and $P^c$ are the orthogonal projections onto $\mathfrak H_{pp}$ and $\mathfrak H_c$.
--
--   **Formalization Note.** The same projection-valued measure $P$ as in the RAGE theorem is taken as data. The iterated limits mean: for each $n$ the limit as $T \to \infty$ (a vector of $\mathfrak H$, Bochner integral) exists, and the sequence of these limits converges to the stated vector.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 130, Corollary 5.9, Eqs. (5.19)–(5.20)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Shared_IsSpectralIntegral
import Definitions.Def_TeschlQM_Shared_timeEvolution
import Definitions.Def_TeschlQM_Dynamics_spectralSubspaces
import Definitions.Def_TeschlQM_Dynamics_IsRelativelyCompact

open Filter Topology

namespace TeschlQM.Dynamics

/-- Teschl, Corollary 5.9, p. 130, (5.19)–(5.20): under the assumptions of the RAGE theorem
(`A = ∫ λ dP(λ)` self-adjoint, `K_n ∈ 𝔏(ℌ)` relatively compact, `K_n → 𝕀` strongly), for every
`ψ ∈ ℌ`: `lim_{n→∞} lim_{T→∞} (1/T) ∫₀ᵀ e^{itA} K_n e^{−itA} ψ dt = P^{pp} ψ` and
`lim_{n→∞} lim_{T→∞} (1/T) ∫₀ᵀ e^{itA} (𝕀 − K_n) e^{−itA} ψ dt = P^c ψ` (iterated limits: each
inner limit exists and the resulting sequence converges). `P^{pp}`, `P^c` are the orthogonal
projections onto `ℌ_pp`, `ℌ_c`. -/
theorem rage_heisenberg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (P : Set ℝ → (H →L[ℂ] H)) (hP : TeschlQM.Shared.IsProjValuedMeasure P)
    (hAP : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) A)
    (K : ℕ → H →L[ℂ] H) (hK : ∀ n, IsRelativelyCompact ((K n : H →ₗ[ℂ] H).toPMap ⊤) A)
    (hKI : ∀ ψ : H, Tendsto (fun n => K n ψ) atTop (𝓝 ψ)) (ψ : H) :
    (∃ L : ℕ → H,
      (∀ n, Tendsto (fun T : ℝ => (1 / T) • ∫ t in (0 : ℝ)..T,
          TeschlQM.Shared.timeEvolution P (-t) (K n (TeschlQM.Shared.timeEvolution P t ψ))) atTop (𝓝 (L n))) ∧
      Tendsto L atTop (𝓝 (orthProj (hpp P) ψ))) ∧
    (∃ L : ℕ → H,
      (∀ n, Tendsto (fun T : ℝ => (1 / T) • ∫ t in (0 : ℝ)..T,
          TeschlQM.Shared.timeEvolution P (-t) (TeschlQM.Shared.timeEvolution P t ψ - K n (TeschlQM.Shared.timeEvolution P t ψ))) atTop
          (𝓝 (L n))) ∧
      Tendsto L atTop (𝓝 (orthProj (hc P) ψ))) := by sorry

end TeschlQM.Dynamics

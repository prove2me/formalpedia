-- Prove2me | Theorems.Thm_QuantumNoise_uncertainty_relation
-- name    : QuantumNoise.uncertainty_relation
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:25:12.222669+00:00
-- url     : https://prove2.me/theorems/2d035d71-52e2-4608-a226-2b1c99c24fb2
-- title:
--   Eq. (4.13) — uncertainty relation with the anticommutator term
-- statement:
--   Let $\rho$ be a state on a unital $\ast$-algebra over $\mathbb C$, and let $\hat A,\hat B$ be self-adjoint with $\langle\hat A\rangle=\langle\hat B\rangle=0$. Write $(\Delta A)^2=\langle\hat A^2\rangle$ and $(\Delta B)^2=\langle\hat B^2\rangle$. Then
--   $$
--   (\Delta A)^2(\Delta B)^2\ \ge\ \frac14\big\langle\{\hat A,\hat B\}\big\rangle^2+\frac14\big|\big\langle[\hat A,\hat B]\big\rangle\big|^2 .
--   $$
--   This is the general Heisenberg uncertainty relation (Gottfried 1966) that the paper applies to cosine transforms of $\hat I$ and $\hat F$ to derive the quantum noise inequality.
--
--   **Formalization Note** $\langle\hat A^2\rangle$, $\langle\hat B^2\rangle$ are real and enter through their real parts; $\langle\{\hat A,\hat B\}\rangle$ is real and its square is written $|\langle\{\hat A,\hat B\}\rangle|^2$.
--
--   Differences from the source:
--   - generalization: expectations ⟨·⟩ of Hermitian operators in a quantum state → any state ρ on any unital ∗-algebra over ℂ (IsState); reason: a density-matrix expectation on bounded or unbounded operators is such a state
--   - encoding: ⟨{Â, B̂}⟩² and (ΔA)² = ⟨Â²⟩ → ‖ρ(ÂB̂ + B̂Â)‖² and Re ρ(Â Â); reason: both quantities are real, so the modulus and the real part change no instance
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. IV.A.3, Eq. (4.13), p.23

import Mathlib
import Definitions.Def_QuantumNoise_IsState

namespace QuantumNoise

/-- **Eq. (4.13)**, the Heisenberg uncertainty relation with the anticommutator term (Clerk et al.,
arXiv:0810.4729v2, Sec. IV.A.3, p.23; printed p.23 = PDF p.23, citing Gottfried 1966): for
Hermitian `Â`, `B̂` with `⟨Â⟩ = ⟨B̂⟩ = 0`,
`(ΔA)² (ΔB)² ≥ ¼ ⟨{Â, B̂}⟩² + ¼ |⟨[Â, B̂]⟩|²`, where `(ΔA)² = ⟨Â²⟩`, `(ΔB)² = ⟨B̂²⟩`.

**Formalization Note** The expectation is any state `ρ` on any unital ∗-algebra over `ℂ`
(`IsState`). `⟨Â²⟩`, `⟨B̂²⟩` are real by positivity and enter through `.re`; `⟨{Â, B̂}⟩` is real and
`⟨{Â, B̂}⟩²` is written `‖⟨{Â, B̂}⟩‖²`. -/
theorem uncertainty_relation {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
    (ρ : 𝒜 →ₗ[ℂ] ℂ) (hρ : IsState ρ) (A B : 𝒜) (hA : star A = A) (hB : star B = B)
    (hA0 : ρ A = 0) (hB0 : ρ B = 0) :
    (1 / 4 : ℝ) * ‖ρ (A * B + B * A)‖ ^ 2 + (1 / 4 : ℝ) * ‖ρ (A * B - B * A)‖ ^ 2 ≤
      (ρ (A * A)).re * (ρ (B * B)).re := by sorry

end QuantumNoise

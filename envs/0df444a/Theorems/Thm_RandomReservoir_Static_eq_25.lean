-- Prove2me | Theorems.Thm_RandomReservoir_Static_eq_25
-- name    : RandomReservoir.Static.eq_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:53.50719+00:00
-- url     : https://prove2.me/theorems/9d09c6e9-21bf-4741-81db-de531b3085c7
-- title:
--   (25), Proof of Theorem 1, Step 2, p. 40 — mean-square error of the i.i.d. average = (1/N) Var(V₁σ(⟨A₁,z⟩+ζ₁)) ≤ (1/N) E[V₁²σ²]
-- statement:
--   Let $\mathcal X$ be a separable real Hilbert space, $N\ge1$, $\pi$ a probability measure on $\mathcal X\times\mathbb R$, $\varphi:\mathcal X\times\mathbb R\to\mathbb R$ measurable, and $z\in\mathcal X$. Let $U_i=(A_i,\zeta_i)$, $i=1,\dots,N$, be i.i.d. with law $\pi$, and $V_i=\varphi(U_i)$. Assume that $V_1\sigma(\langle A_1,z\rangle+\zeta_1)$ is square-integrable with mean $c$ (in the proof, $c=H^*(z)$ by (20) and (21)). Then
--   $$\mathbb E\Big[\Big|\frac1N\sum_{i=1}^NV_i\sigma(\langle A_i,z\rangle+\zeta_i)-c\Big|^2\Big]=\frac1N\operatorname{Var}\big(V_1\sigma(\langle A_1,z\rangle+\zeta_1)\big)\le\frac1N\,\mathbb E\big[V_1^2\sigma(\langle A_1,z\rangle+\zeta_1)^2\big].$$
--
--   This is the Monte Carlo step of the proof: with the readout $W=\frac1N(V_1\ \cdots\ V_N)$ of (23), the network $H_W^{A,\zeta}(z)$ is the sample average on the left.
--
--   **Formalization Note.** The $N$ i.i.d. samples are the coordinates of the product measure $\pi^{\otimes N}$ on $(\mathcal X\times\mathbb R)^N$. The variance is Mathlib's `ProbabilityTheory.variance`, finite here by square-integrability. $N\ge1$ is required: for $N=0$ the left side is $c^2$.
-- source:
--   Gonon, Grigoryeva & Ortega, Ann. Appl. Probab. 33 (2023), Proof of Theorem 1, Step 2, p. 40, (22), (23), (25)

import Mathlib
import Definitions.Def_RandomReservoir_Static_Setting

namespace RandomReservoir.Static

open MeasureTheory ProbabilityTheory

/-- (25), Proof of Theorem 1, Step 2, p. 40 (Gonon–Grigoryeva–Ortega, Ann. Appl. Probab. 33 (2023)):
if `U_1, …, U_N` are i.i.d. with law `π` on `𝒳 × ℝ`, `V_i = φ(U_i)`, and the summand
`φ(w,u) σ(⟨w,z⟩ + u)` is square-integrable with mean `c` (in the proof, `c = H*(z)`), then the
mean-square error of the sample average equals `(1/N) Var(V_1 σ(⟨A_1,z⟩ + ζ_1))`, which is at most
`(1/N) E[V_1² σ(⟨A_1,z⟩ + ζ_1)²]`. -/
theorem eq_25
    {𝒳 : Type*} [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [CompleteSpace 𝒳]
    [TopologicalSpace.SeparableSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    (N : ℕ) (hN : 0 < N)
    (π : Measure (𝒳 × ℝ)) [IsProbabilityMeasure π]
    (φ : 𝒳 × ℝ → ℝ) (hφ : Measurable φ) (z : 𝒳) (c : ℝ)
    (hL2 : MemLp (fun p : 𝒳 × ℝ => φ p * relu (inner ℝ p.1 z + p.2)) 2 π)
    (hc : ∫ p, φ p * relu (inner ℝ p.1 z + p.2) ∂π = c) :
    ∫ θ, ((1 / (N : ℝ)) * ∑ i, φ (θ i) * relu (inner ℝ (θ i).1 z + (θ i).2) - c) ^ 2
        ∂(Measure.pi fun _ : Fin N => π)
      = (1 / (N : ℝ)) * variance (fun p : 𝒳 × ℝ => φ p * relu (inner ℝ p.1 z + p.2)) π ∧
    (1 / (N : ℝ)) * variance (fun p : 𝒳 × ℝ => φ p * relu (inner ℝ p.1 z + p.2)) π
      ≤ (1 / (N : ℝ)) * ∫ p, φ p ^ 2 * relu (inner ℝ p.1 z + p.2) ^ 2 ∂π := by sorry

end RandomReservoir.Static

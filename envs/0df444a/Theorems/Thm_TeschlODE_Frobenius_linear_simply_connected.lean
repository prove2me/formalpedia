-- Prove2me | Theorems.Thm_TeschlODE_Frobenius_linear_simply_connected
-- name    : TeschlODE.Frobenius.linear_simply_connected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:18:06.340818+00:00
-- url     : https://prove2.me/theorems/af71e3e4-d598-4d7d-916f-4f1470f51554
-- title:
--   Theorem 4.7 — linear analytic systems on a simply connected domain have global solutions
-- statement:
--   Let $\Omega \subseteq \mathbb{C}$ be a simply connected domain, and let $A : \Omega \to \mathbb{C}^{n \times n}$ and $b : \Omega \to \mathbb{C}^n$ be analytic. Then for every $z_0 \in \Omega$ and $w_0 \in \mathbb{C}^n$ the initial value problem
--   $$w'(z) = A(z)\,w(z) + b(z), \qquad w(z_0) = w_0,$$
--   has a unique solution defined on all of $\Omega$. In particular, the power series at $z_0$ of every solution converges in the largest disc centred at $z_0$ and contained in $\Omega$.
--
--   The theorem shows that solutions of a linear equation can be singular only where the coefficients are, which is why Section 4.3 can study solutions near an isolated singularity of $A$.
--
--   **Formalization Note.** $\Omega$ is an open set with `SimplyConnectedSpace Ω` (nonempty, path connected, trivial fundamental group). $A$ is analytic entrywise (`DifferentiableOn ℂ` for each entry) and $b$ is `DifferentiableOn ℂ` on $\Omega$. Vectors are `Fin n → ℂ`, $A(z)w$ is `Matrix.mulVec`. The statement has three parts: existence of $w$ with $w(z_0) = w_0$ and complex derivative $A(z)w(z) + b(z)$ at every $z \in \Omega$; any two such solutions agree on $\Omega$; and every solution on $\Omega$ has a power series at $z_0$ that converges to it on the disc of radius $\operatorname{dist}(z_0, \mathbb{C} \setminus \Omega)$ (`Metric.infEDist z₀ Ωᶜ`, which is $\infty$ when $\Omega = \mathbb{C}$).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 130, Theorem 4.7

import Mathlib

open Matrix

namespace TeschlODE.Frobenius

/-- Teschl, Theorem 4.7 (p. 130): let `A : Ω → ℂ^{n×n}` and `b : Ω → ℂⁿ` be analytic on a simply
connected domain `Ω ⊆ ℂ` (open; `SimplyConnectedSpace Ω` includes nonempty and path connected).
Then for every `z₀ ∈ Ω` and `w₀ ∈ ℂⁿ` the initial value problem `w' = A(z) w + b(z)`,
`w(z₀) = w₀` has a solution defined on all of `Ω`, any two such solutions agree on `Ω`, and the
power series at `z₀` of every solution on `Ω` converges to it on the largest disc centred at
`z₀` contained in `Ω` (radius `infEDist z₀ Ωᶜ`, `= ⊤` when `Ω = ℂ`). -/
theorem linear_simply_connected (n : ℕ) (A : ℂ → Matrix (Fin n) (Fin n) ℂ) (b : ℂ → Fin n → ℂ)
    (Ω : Set ℂ) (hΩo : IsOpen Ω) (hΩ : SimplyConnectedSpace Ω)
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) Ω) (hb : DifferentiableOn ℂ b Ω)
    (z₀ : ℂ) (hz₀ : z₀ ∈ Ω) (w₀ : Fin n → ℂ) :
    (∃ w : ℂ → Fin n → ℂ, w z₀ = w₀ ∧ ∀ z ∈ Ω, HasDerivAt w (A z *ᵥ w z + b z) z) ∧
    (∀ w v : ℂ → Fin n → ℂ, w z₀ = w₀ → v z₀ = w₀ →
      (∀ z ∈ Ω, HasDerivAt w (A z *ᵥ w z + b z) z) →
      (∀ z ∈ Ω, HasDerivAt v (A z *ᵥ v z + b z) z) → Set.EqOn w v Ω) ∧
    (∀ w : ℂ → Fin n → ℂ, (∀ z ∈ Ω, HasDerivAt w (A z *ᵥ w z + b z) z) →
      ∃ ph : FormalMultilinearSeries ℂ ℂ (Fin n → ℂ),
        HasFPowerSeriesOnBall w ph z₀ (Metric.infEDist z₀ Ωᶜ)) := by sorry

end TeschlODE.Frobenius

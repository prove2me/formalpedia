-- Prove2me | Theorems.Thm_PersuadeFly_lemma_5
-- name    : PersuadeFly.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:32:07.766966+00:00
-- url     : https://prove2.me/theorems/075a3a1e-d531-4def-b6f3-ec4d01c4bd0b
-- title:
--   Lemma 5, p.40 — on $\{\mu^*\in\mathcal B_t\}$, $\mathsf{Gap}(\gamma_t,\mathcal B_t)\le\frac{16}{p_0^2D}\,\epsilon_t$
-- statement:
--   Let the instance satisfy the regularity conditions with constants $D$ and $p_0$.
--
--   1. ($t\ge1$.) For every $\gamma\in\Delta(\Omega)$, every $\mu^*\in\mathcal B_0$ and every $\epsilon>0$ with $\mu^*\in\mathsf B_1(\gamma,\epsilon)$,
--   $$
--   \mathsf{Gap}\big(\gamma,\mathsf B_1(\gamma,\epsilon)\big)\le\frac{16}{p_0^2D}\,\epsilon .
--   $$
--   2. ($t=0$.) For every $\gamma_0\in\mathcal B_0$ and every first-round set $\mathcal C_0$ with $\mathcal B_0\subseteq\mathcal C_0\subseteq\Delta(\Omega)$,
--   $$
--   \mathsf{Gap}(\gamma_0,\mathcal C_0)\le\frac{16}{p_0^2D}\cdot2 .
--   $$
--
--   Applied to $\gamma=\gamma_t$, $\epsilon=\epsilon_t$, this is Lemma 5 of the paper: on the event that the confidence set $\mathcal B_t$ contains $\mu^*$, the cost of robust persuasion paid by Rai at time $t$ is linear in the radius $\epsilon_t$.
--
--   Differences from the source:
--   - generalization: γ_t (an empirical distribution) and the radius ϵ_t of Theorem 2, t ≥ 1 → every γ ∈ Δ(Ω) and every ϵ > 0; reason: γ_t ∈ Δ(Ω) and ϵ_t > 0, so the source's case is an instance
--   - reading: ϵ₀, which the formula leaves undefined at t = 0 (division by zero) → ϵ₀ = 2 in clause 2; reason: the proof of Theorem 2 uses ϵ₀ = 2 (the term "2 +" on p.38) and p.20 calls B₀ an ℓ₁-ball at γ₀
--   - generalization: first confidence set: B₀ (Algorithm 1's box) or B₁(γ₀, ϵ₀) = Δ(Ω) (text of p.20 and the proofs) → any set C₀ with B₀ ⊆ C₀ ⊆ Δ(Ω); reason: both readings are instances of C₀
--   - generalization: D the largest radius in Assumption 1 → any radius D for which Assumption 1.1 holds; reason: the largest radius is admissible, so the printed statement is the instance D = largest
--   - encoding: the event {μ* ∈ B_t} → the hypothesis μ* ∈ B₁(γ, ϵ) (clause 1); at t = 0 μ* ∈ B₀ ⊆ C₀ always (clause 2); reason: the bound is a deterministic statement on that event
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Lemma 5, p.40

import Mathlib
import Definitions.Def_PersuadeFly_IsRegular
import Definitions.Def_PersuadeFly_gap

namespace PersuadeFly

/-- **Lemma 5.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Lemma 5, p.40: for `t ∈ [T]`, on the event `{μ* ∈ B_t}`,
`Gap(γ_t, B_t) ≤ (16 / (p₀² D)) ϵ_t`.

**Formalization Note** Clause 1 is the case `t ≥ 1`, where `B_t = B₁(γ_t, ϵ_t)`, stated for every
`γ ∈ Δ(Ω)` and every radius `ϵ > 0` (`γ_t` is a distribution and `ϵ_t > 0`). Clause 2 is the case
`t = 0`, where the first set is `C₀` with `B₀ ⊆ C₀ ⊆ Δ(Ω)` (so `μ* ∈ C₀` always) and `ϵ₀ = 2`, the
value the proof of Theorem 2 uses (p.38: the term `2 +`). -/
theorem lemma_5 {Ω A : Type} [Fintype Ω] [Nontrivial Ω] [Fintype A] [Nontrivial A]
    (I : Instance Ω A) (D p0 : ℝ) (hreg : IsRegular I D p0) :
    (∀ γ : Ω → ℝ, γ ∈ stdSimplex ℝ Ω → ∀ μ ∈ I.B0, ∀ ϵ : ℝ, 0 < ϵ → μ ∈ ball1 γ ϵ →
      gap I γ (ball1 γ ϵ) ≤ 16 / (p0 ^ 2 * D) * ϵ) ∧
    (∀ γ0 ∈ I.B0, ∀ C0 : Set (Ω → ℝ), I.B0 ⊆ C0 → C0 ⊆ stdSimplex ℝ Ω →
      gap I γ0 C0 ≤ 16 / (p0 ^ 2 * D) * 2) := by sorry

end PersuadeFly

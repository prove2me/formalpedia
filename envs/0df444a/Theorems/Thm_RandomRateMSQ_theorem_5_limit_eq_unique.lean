-- Prove2me | Theorems.Thm_RandomRateMSQ_theorem_5_limit_eq_unique
-- name    : RandomRateMSQ.theorem_5_limit_eq_unique
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:16.722025+00:00
-- url     : https://prove2.me/theorems/fcd68a3b-bc80-462d-98c0-9077366e7449
-- title:
--   Proof of Theorem 5 — the limit equation (3.7) has a unique solution, pathwise
-- statement:
--   Let $x_0\in\mathbb R$, let $w:[0,\infty)\to\mathbb R$ and $c:[0,\infty)\to\mathbb R$ be measurable and bounded on every $[0,T]$, and let $b,\gamma\in\mathbb R$. Then there is exactly one measurable $\xi:[0,\infty)\to\mathbb R$, bounded on every $[0,T]$, with
--
--   $$
--   \xi(t)=x_0+w(t)+b\,t+c(t)\int_0^t\xi^-(s)\,ds-\gamma\int_0^t\xi^+(s)\,ds\qquad\text{for all }t\ge0 .
--   $$
--
--   Applied path by path with $w$ the Brownian noise, $b=\hat\lambda-\tilde\sigma$, $c(t)=\langle\!\langle\iota,\eta_t\rangle\!\rangle$ and $\gamma\ge0$, this is the solution $\breve\xi$ of the limit equation used in the proof of Theorem 5.
--
--   Differences from the source:
--   - generalization: the equation with w a Brownian path times √(µ̄(1+var u)), γ ≥ 0 and c(t) = ⟨⟨ι, ηₜ⟩⟩ ≥ 0 → every measurable locally bounded w and c and every real b, γ; reason: uniqueness and existence hold by a Volterra/Gronwall argument for any locally bounded coefficients; the source's case is an instance
--   - reading: the unique strong solution → the unique measurable solution bounded on every [0, T], pathwise; reason: (3.7) has constant diffusion coefficient and no stochastic integral, so a strong solution is a pathwise solution
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, proof of Theorem 5, p.18 ("Let ξ̆(t) be the unique strong solution of …")

import Mathlib
import Definitions.Def_RandomRateMSQ_SolvesLimitEq

open MeasureTheory
open scoped NNReal

namespace RandomRateMSQ

/-- **Unique solvability of the limit equation (3.7)** (Büke–Qin, arXiv:1905.04198v1, proof of
Theorem 5, p.18: "Let ξ̆(t) be the unique strong solution of …"), pathwise and in greater
generality: for every `x₀ ∈ ℝ`, every measurable locally bounded `w : ℝ₊ → ℝ`, every `b, γ ∈ ℝ`
and every measurable locally bounded `c : ℝ₊ → ℝ`, there is exactly one measurable locally bounded
`ξ` with `ξ(t) = x₀ + w(t) + b t + c(t) ∫₀ᵗ ξ⁻ − γ ∫₀ᵗ ξ⁺` for all `t ≥ 0`.

**Formalization Note.** In the paper `w` is a Brownian path times a constant, `γ ≥ 0` and
`c(t) = ⟨⟨ι, ηₜ⟩⟩ ≥ 0`; the statement covers every such instance. -/
theorem theorem_5_limit_eq_unique (x₀ : ℝ) (w : ℝ≥0 → ℝ) (hw : Measurable w)
    (hwb : ∀ T : ℝ≥0, ∃ K : ℝ, ∀ t : ℝ≥0, t ≤ T → |w t| ≤ K) (b γ : ℝ) (c : ℝ≥0 → ℝ)
    (hc : Measurable c) (hcb : ∀ T : ℝ≥0, ∃ K : ℝ, ∀ t : ℝ≥0, t ≤ T → |c t| ≤ K) :
    ∃! ξ : ℝ≥0 → ℝ, SolvesLimitEq x₀ w b γ c ξ := by sorry

end RandomRateMSQ

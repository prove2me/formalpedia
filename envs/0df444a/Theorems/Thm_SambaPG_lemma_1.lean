-- Prove2me | Theorems.Thm_SambaPG_lemma_1
-- name    : SambaPG.lemma_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:37:03.667363+00:00
-- url     : https://prove2.me/theorems/93ff368e-f1bb-4821-886b-1fc927606ecf
-- title:
--   Lemma 1 — $\bar q(t+1)\le\bar q(t)-\eta\bar q(t)^2$ implies $\bar q(t)\le\bar q(0)/(1+\eta\bar q(0)t)$
-- statement:
--   Let $(\bar q(t):t\in\mathbb Z_+)$ be positive real numbers and $\eta>0$ such that
--
--   $$
--   \bar q(t+1)\le\bar q(t)-\eta\,\bar q(t)^2\qquad\text{for all }t .
--   $$
--
--   Then for all $t\in\mathbb Z_+$,
--
--   $$
--   \bar q(t)\le\frac{\bar q(0)}{1+\eta\,\bar q(0)\,t}.
--   $$
--
--   This is the discrete analogue of the differential equation $\dot q=-\eta q^2$, and it turns the drift (12) of the embedded chain into the bound (13).
--
--   Differences from the source: none.
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, Lemma 1, p.8, eq. (7)

import Mathlib

namespace SambaPG

/-- **Lemma 1 (discrete analogue of `q̇ = −η q²`).**
Denisov & Walton, arXiv:2007.10229v3, Lemma 1, p.8, eq. (7).

If `(q̄(t) : t ∈ ℤ₊)` is a sequence of positive reals with `q̄(t + 1) ≤ q̄(t) − η q̄(t)²` for all `t`
and some `η > 0`, then `q̄(t) ≤ q̄(0) / (1 + η q̄(0) t)` for all `t ∈ ℤ₊`. -/
theorem lemma_1 (qbar : ℕ → ℝ) (hpos : ∀ t, 0 < qbar t) {η : ℝ} (hη : 0 < η)
    (h7 : ∀ t, qbar (t + 1) ≤ qbar t - η * qbar t ^ 2) :
    ∀ t : ℕ, qbar t ≤ qbar 0 / (1 + η * qbar 0 * t) := by sorry

end SambaPG

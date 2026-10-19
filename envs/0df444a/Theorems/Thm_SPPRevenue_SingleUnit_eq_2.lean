-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_eq_2
-- name    : SPPRevenue.SingleUnit.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:59.858911+00:00
-- url     : https://prove2.me/theorems/471bc214-8d77-46fb-99ed-70cc2245c46f
-- title:
--   Inequality (2), p. 14 — the uniform price τ earns at least τ·s⋆(τ), so max_{τ≥0} τ s⋆(τ) ≤ UP; and s⋆ ≤ 1
-- statement:
--   Let $t$ be a single-unit threshold mechanism for $n$ buyers with independent values. Then:
--   1. for every $\tau \ge 0$, the sequential posted-price mechanism that posts the uniform price $\tau$ to every buyer earns at least $\tau\, s^\star(\tau)$;
--   2. consequently
--   $$\sup_{\tau \ge 0} \tau\, s^\star(\tau) \le \mathrm{UP};$$
--   3. $s^\star(\tau) \le 1$ for every $\tau$.
--
--   These are the first set of constraints of the factor-revealing program: they show that $s^\star$, normalized by the better of the two pricing rules, satisfies $s^\star(\tau) \le \min(1, 1/\tau)$.
--
--   **Formalization Note** The printed display also has "$\mathrm{UP} \le 1$", which is the proof's normalization $\max(\mathrm{MP},\mathrm{UP}) = 1$, not a statement about the model; it is not part of this theorem. Part 3 uses the almost-sure single-unit feasibility of the thresholds; the page states it for $\tau \ge 0$, and it holds for all $\tau$.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 14, §4.1, Inequality (2)

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting

namespace SPPRevenue.SingleUnit

open MeasureTheory
open scoped ENNReal

theorem eq_2 {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (t : Fin n → (Fin n → ℝ) → ℝ) (ht : IsThresholdMech μ t) :
    (∀ τ : ℝ, 0 ≤ τ → ENNReal.ofReal τ * sStar μ t τ ≤ sppRev μ (fun _ => τ)) ∧
      (⨆ (τ : ℝ) (_ : 0 ≤ τ), ENNReal.ofReal τ * sStar μ t τ) ≤ upRev μ ∧
      ∀ τ : ℝ, sStar μ t τ ≤ 1 := by sorry

end SPPRevenue.SingleUnit

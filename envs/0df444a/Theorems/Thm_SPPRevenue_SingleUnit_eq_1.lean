-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_eq_1
-- name    : SPPRevenue.SingleUnit.eq_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:53.840148+00:00
-- url     : https://prove2.me/theorems/aa03224c-dea0-415a-9c0a-d16308ba54a7
-- title:
--   Equation (1), p. 12 — Opt = ∫_0^∞ s⋆(τ) dτ, and s⋆ is weakly decreasing
-- statement:
--   Let $t$ be a family of measurable, nonnegative thresholds for $n$ buyers with independent values, and let $s^\star(\tau) = \sum_i \mathbb P[v_i \ge t_i \ge \tau]$. Then the expected revenue of the threshold mechanism equals the integral of $s^\star$:
--   $$\mathrm{Opt} = \mathbb E\Big[\sum_i t_i\,\mathbf 1\{v_i \ge t_i\}\Big] = \int_0^\infty s^\star(\tau)\,d\tau,$$
--   and $s^\star$ is weakly decreasing.
--
--   The paper takes this formula as the definition of $\mathrm{Opt}$; here $\mathrm{Opt}$ is the expected payment, and the formula is the theorem connecting the two. It is how the optimal revenue enters the factor-revealing program.
--
--   **Formalization Note** Only measurability and nonnegativity of the thresholds are assumed; single-unit feasibility is not needed for this identity. The integral is over $(0,\infty)$ and lives in $[0,\infty]$.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 12, §3.2, Equation (1)

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting

namespace SPPRevenue.SingleUnit

open MeasureTheory
open scoped ENNReal

theorem eq_1 {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (t : Fin n → (Fin n → ℝ) → ℝ) (hmeas : ∀ i, Measurable (t i))
    (hnonneg : ∀ i v, 0 ≤ t i v) :
    optRev μ t = ∫⁻ τ in Set.Ioi 0, sStar μ t τ ∧ Antitone (sStar μ t) := by sorry

end SPPRevenue.SingleUnit

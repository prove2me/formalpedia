-- Prove2me | Theorems.Thm_ServTimeLimit_OptMech_revenue_le_first_best
-- name    : ServTimeLimit.OptMech.revenue_le_first_best
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:51.669997+00:00
-- url     : https://prove2.me/theorems/0a56fe4a-3f1d-4b21-9b8a-86508e0cfc60
-- title:
--   Proof of Theorem 8, p. 47 — the revenue of an IR mechanism is bounded by the social welfare of its allocation, hence by the first best
-- statement:
--   Assume $\Lambda, c, \bar\theta > 0$, and let $(\Phi, t, p)$ be a direct mechanism (a feasible allocation with a measurable, integrable, non-negative price) that is individually rational. Then
--   $$\pi(\Phi, p) = \frac{\Lambda}{\bar\theta}\int_\Phi p(\theta)\,d\theta \;\le\; SW(\Phi, t),$$
--   and consequently $\pi(\Phi, p) \le SW(\Phi^*, t^*)$ for every first-best allocation $(\Phi^*, t^*)$.
--
--   This is the upper half of Theorem 8: no mechanism the firm can run earns more than the first-best welfare.
-- source:
--   Feldman & Segev, The Important Role of Time Limits when Consumers Choose their Time in Service, SSRN 3424317 (version of 2021-10-07), p. 47, proof of Theorem 8

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model

namespace ServTimeLimit.OptMech

open MeasureTheory

/-- Proof of Theorem 8, p. 47: the revenue of a feasible individually rational
mechanism is at most the social welfare of its allocation, and hence at most the first-best
welfare. -/
theorem revenue_le_first_best (P : Params) (hP : P.Standing) (Φ : Set ℝ) (t p : ℝ → ℝ)
    (hM : IsMechanism P Φ t p) (hIR : IsIR P Φ t p) :
    revenue P Φ p ≤ welfare P Φ t ∧
    ∀ (Φs : Set ℝ) (ts : ℝ → ℝ), IsFirstBest P Φs ts → revenue P Φ p ≤ welfare P Φs ts := by sorry

end ServTimeLimit.OptMech

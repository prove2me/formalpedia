-- Prove2me | Theorems.Thm_TIESharp_bsSlotLaw_exists
-- name    : TIESharp.bsSlotLaw_exists
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:18:51.455944+00:00
-- url     : https://prove2.me/theorems/a5164ef5-c905-4a2e-861b-c333dc694e35
-- title:
--   Existence of a Bounded-Square slot-rounding law
-- statement:
--   For every $n\ge2$, every finite job count $m$, and every nonnegative processing-time profile $t$, there is a probability law $y$ on integral assignments whose job--machine marginals are the Bounded-Square probabilities and whose support consists of slot-feasible assignments.
--
--   This is the distribution obtained by filling the deficits of the job--slot matrix with dummy rows, decomposing it into perfect matchings, and drawing a matching according to its weight. The empty instance has its empty assignment.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, Theorem 3.3 mechanism, §3.2, p.10; finite distribution over matchings, §5.2, p.23 (standing n≥2, §2, p.4).

import Mathlib
import Definitions.Def_TIESharp_Nonneg
import Definitions.Def_TIESharp_IsBSSlotLaw

set_option autoImplicit false

/-- Existence of the slot-rounding distribution constructed by matching decomposition
(Li, *Sharp Bounds for Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §3.2, p.10,
and §5.2, p.23). -/
theorem TIESharp.bsSlotLaw_exists (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (t : Fin n → Fin m → ℝ)
    (ht : TIESharp.Nonneg t) : ∃ y : (Fin m → Fin n) → ℝ, TIESharp.IsBSSlotLaw t y := by sorry

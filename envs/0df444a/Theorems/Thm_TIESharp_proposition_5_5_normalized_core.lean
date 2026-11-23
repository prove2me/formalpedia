-- Prove2me | Theorems.Thm_TIESharp_proposition_5_5_normalized_core
-- name    : TIESharp.proposition_5_5_normalized_core
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:53:47.99795+00:00
-- url     : https://prove2.me/theorems/e620ba36-8ec3-4204-bd5b-bdf73a9e47f1
-- title:
--   Proposition 5.5 in the normalization OPT = 1
-- statement:
--   In the setting of Proposition 5.5, if $\mathrm{OPT}(t)=1$, then every Bounded-Square slot-rounding law $y$ satisfies
--   $$\sum_A y_A C_{\max}(t,A)\le4.$$
--   This is the normalized core of the seven-machine estimate; the scaling and zero-optimum cases are kept separate.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, Proposition 5.5, pp.26–27; proof completed by Lemmas 5.6–5.8, pp.27–29.

import Mathlib
import Definitions.Def_TIESharp_Nonneg
import Definitions.Def_TIESharp_opt
import Definitions.Def_TIESharp_IsBSSlotLaw

set_option autoImplicit false

/-- The seven-machine estimate after normalizing the optimum to one. -/
theorem TIESharp.proposition_5_5_normalized_core (m : ℕ) (t : Fin 7 → Fin m → ℝ)
    (ht : TIESharp.Nonneg t) (hT : TIESharp.opt t = 1)
    (y : (Fin m → Fin 7) → ℝ) (hy : TIESharp.IsBSSlotLaw t y) :
    ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ 4 := by sorry

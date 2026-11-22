-- Prove2me | Theorems.Thm_SZ_eventually_composite
-- name    : SZ.eventually_composite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:52:27.096801+00:00
-- url     : https://prove2.me/theorems/4a74ca11-1b6e-4e9c-b19b-d8f1ae94f2ed
-- title:
--   SZ: eventually composite
-- statement:
--   **The composite corollary of the design.**  For every modulus `m ≥ 2` admitted by the
--   design, all but finitely many integral parts `⌊ξ αⁿ⌋` are composite.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadraticDesign.lean#L70-L83
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadraticDesign.lean#L70-L83

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_SZ_QuadraticDesign
set_option autoImplicit false
open SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}

theorem SZ.eventually_composite {m : ℤ} (h : Pair α β a b) (hβ : β < 0) (hm : 2 ≤ m)
    (ha : m ∣ a) (hb : m ∣ (b - 1)) :
    ∀ᶠ n in atTop, ¬ Prime ⌊xiDesign α β * α ^ n⌋ ∧ 1 < ⌊xiDesign α β * α ^ n⌋ := by sorry

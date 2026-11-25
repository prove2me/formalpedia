-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_inv
-- name    : ReciprocityTheory.ChartRestriction.G.T0.wa_inv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:16:44.624968+00:00
-- url     : https://prove2.me/theorems/cf19d4d4-1c64-4fff-b126-27d8a8dc57a7
-- title:
--   T0: wa inv
-- statement:
--   The T0 construction uses the wa inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L38-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L38-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Filter
variable {F : Type*} [Field F]

theorem ReciprocityTheory.ChartRestriction.G.T0.wa_inv (w : AddValuation F (WithTop ℤ)) {a : F} {m : ℤ} (ha : w a = m) :
    w a⁻¹ = ((-m : ℤ) : WithTop ℤ) := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_ne_zero_of_coe
-- name    : ReciprocityTheory.ChartRestriction.G.T0.wa_ne_zero_of_coe
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:16:53.819795+00:00
-- url     : https://prove2.me/theorems/af4de105-27a8-4732-9a6c-ab424e5ee1b2
-- title:
--   T0: wa ne zero of coe
-- statement:
--   The T0 construction uses the wa ne zero of coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L16-L20

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

theorem ReciprocityTheory.ChartRestriction.G.T0.wa_ne_zero_of_coe (w : AddValuation F (WithTop ℤ)) {a : F} {m : ℤ} (h : w a = m) :
    a ≠ 0 := by sorry

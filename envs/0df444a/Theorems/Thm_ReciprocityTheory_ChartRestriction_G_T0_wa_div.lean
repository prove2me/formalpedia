-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_div
-- name    : ReciprocityTheory.ChartRestriction.G.T0.wa_div
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:20:08.831259+00:00
-- url     : https://prove2.me/theorems/f06834b9-7748-4676-8096-14098c87793c
-- title:
--   T0: wa div
-- statement:
--   The T0 construction uses the wa div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L52-L54

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

theorem ReciprocityTheory.ChartRestriction.G.T0.wa_div (w : AddValuation F (WithTop ℤ)) {a b : F} {m n : ℤ} (ha : w a = m)
    (hb : w b = n) : w (a / b) = ((m - n : ℤ) : WithTop ℤ) := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_zpow
-- name    : ReciprocityTheory.ChartRestriction.G.T0.wa_zpow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:27:53.382293+00:00
-- url     : https://prove2.me/theorems/499fc457-df66-4d1d-b5dd-d9143f7d62c1
-- title:
--   T0: wa zpow
-- statement:
--   The T0 construction uses the wa zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L56-L62

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

theorem ReciprocityTheory.ChartRestriction.G.T0.wa_zpow (w : AddValuation F (WithTop ℤ)) {a : F} {m : ℤ} (h : w a = m) (z : ℤ) :
    w (a ^ z) = ((z * m : ℤ) : WithTop ℤ) := by sorry

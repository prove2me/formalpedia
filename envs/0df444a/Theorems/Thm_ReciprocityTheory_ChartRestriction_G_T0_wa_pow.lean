-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_pow
-- name    : ReciprocityTheory.ChartRestriction.G.T0.wa_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:47.126424+00:00
-- url     : https://prove2.me/theorems/562ee70d-c4a7-4aa2-a08f-eb2545d0d757
-- title:
--   T0: wa pow
-- statement:
--   The T0 construction uses the wa pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L22-L32

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

theorem ReciprocityTheory.ChartRestriction.G.T0.wa_pow (w : AddValuation F (WithTop ℤ)) {a : F} {m : ℤ} (h : w a = m) (n : ℕ) :
    w (a ^ n) = ((n * m : ℤ) : WithTop ℤ) := by sorry

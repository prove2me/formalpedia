-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_mul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.wa_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:16:58.798804+00:00
-- url     : https://prove2.me/theorems/2d898573-393b-477f-b294-44807b3e0b5e
-- title:
--   T0: wa mul
-- statement:
--   The T0 construction uses the wa mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L34-L36

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

theorem ReciprocityTheory.ChartRestriction.G.T0.wa_mul (w : AddValuation F (WithTop ℤ)) {a b : F} {m n : ℤ} (ha : w a = m)
    (hb : w b = n) : w (a * b) = ((m + n : ℤ) : WithTop ℤ) := by sorry

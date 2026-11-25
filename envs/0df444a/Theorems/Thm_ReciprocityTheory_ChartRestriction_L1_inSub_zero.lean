-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_inSub_zero
-- name    : ReciprocityTheory.ChartRestriction.L1.inSub_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:45:58.981814+00:00
-- url     : https://prove2.me/theorems/3f75180f-6e1e-4a8e-8c57-344ed00d14bc
-- title:
--   L1: in Sub zero
-- statement:
--   The L1 construction uses the in Sub zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorSub.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorSub.lean#L15-L15

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
variable {C : Type} [Field C] (K : Subfield C) (W : WeierstrassCurve C)

theorem ReciprocityTheory.ChartRestriction.L1.inSub_zero : InSub K (0 : W.toAffine.Point) := by sorry

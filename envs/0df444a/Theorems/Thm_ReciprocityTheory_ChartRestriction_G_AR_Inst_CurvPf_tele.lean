-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_tele
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.tele
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:40:59.800797+00:00
-- url     : https://prove2.me/theorems/0b81497c-e646-4592-bdfa-910a93e83bbb
-- title:
--   Curv Pf: tele
-- statement:
--   The Curv Pf construction uses the tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/TelePoint.lean#L49-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/TelePoint.lean#L49-L86

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviLogfk
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_TelePoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.tele (b : Frame X.Ψ r) (z u : V (nd X)) (la : Wt X.Ψ r) (τ : X.Ψ) :
    ∑ i : Fin r, (la τ i : ℝ) * (Ck X b z u τ i.succ - Ck X b z u τ i.castSucc) =
      ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then coef X la τ a j * ‖Yd X b z u τ j a‖ ^ 2 else 0 := by sorry

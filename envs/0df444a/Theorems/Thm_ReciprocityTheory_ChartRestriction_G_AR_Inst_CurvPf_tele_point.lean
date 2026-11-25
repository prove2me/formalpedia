-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_tele_point
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.tele_point
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:57:22.68215+00:00
-- url     : https://prove2.me/theorems/e8904c3a-4e17-4c1e-aedf-3c74d7bfab2a
-- title:
--   Curv Pf: tele point
-- statement:
--   The Curv Pf construction uses the tele point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/TelePoint.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/TelePoint.lean#L32-L37

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.tele_point (a j i : Fin r) :
    ((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
      (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0)) =
      if (a : ℕ) < j then ((if i = a then 1 else 0) - (if i = j then 1 else 0)) else 0 := by sorry

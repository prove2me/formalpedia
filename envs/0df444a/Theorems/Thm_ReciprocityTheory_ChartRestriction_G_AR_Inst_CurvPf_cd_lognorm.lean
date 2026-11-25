-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cd_lognorm
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.cd_lognorm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:04:01.694566+00:00
-- url     : https://prove2.me/theorems/c5f688ee-7732-43b6-93dd-bea7eee05ece
-- title:
--   Curv Pf: cd lognorm
-- statement:
--   The Curv Pf construction uses the cd lognorm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/CurvatureStatementHolds.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/CurvatureStatementHolds.lean#L43-L46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoefNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CurvatureStatementHolds
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
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.cd_lognorm {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (d : F → ℂ) (hd : ContDiff ℝ 2 d)
    (z : F) (hz : d z ≠ 0) : ContDiffAt ℝ 2 (fun w => Real.log ‖d w‖) z := by sorry

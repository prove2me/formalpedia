-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_snd_affine
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.snd_affine
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:57.813151+00:00
-- url     : https://prove2.me/theorems/07324797-8353-546c-b0d4-eb9676b6b292
-- title:
--   Curv Pf: snd affine
-- statement:
--   The Curv Pf construction uses the snd affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LeviVReLine.lean#L12-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LeviVReLine.lean#L12-L34

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LogpdAnalytic
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviVReLine
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
open ReciprocityTheory.AnForm ReciprocityTheory.L2DbarEstimates Filter Topology

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.snd_affine {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (h : F → ℝ) (c : F) (L : E →L[ℝ] F) (x : E) (hh : ContDiffAt ℝ 2 h (c + L x))
    (w : E) :
    fderiv ℝ (fderiv ℝ (fun y => h (c + L y))) x w w = fderiv ℝ (fderiv ℝ h) (c + L x) (L w) (L w) := by sorry

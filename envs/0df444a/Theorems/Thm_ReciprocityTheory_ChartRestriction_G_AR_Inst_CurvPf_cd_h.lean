-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cd_h
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.cd_h
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:05:46.272232+00:00
-- url     : https://prove2.me/theorems/ccc620d8-795b-4888-ad31-4fc89250345a
-- title:
--   Curv Pf: cd h
-- statement:
--   The Curv Pf construction uses the cd h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/CurvatureStatementHolds.lean#L48-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/CurvatureStatementHolds.lean#L48-L65

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.cd_h (x0 : Frame X.Ψ r) (z : V (nd X)) (hz : cpt X x0 z ∈ X.dom) (la : Wt X.Ψ r) :
    ContDiffAt ℝ 2 (fun w => -2 * Real.log (X.nfac la (cpt X x0 w))) z := by sorry

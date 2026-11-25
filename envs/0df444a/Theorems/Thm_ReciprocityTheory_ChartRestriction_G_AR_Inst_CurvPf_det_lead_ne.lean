-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_det_lead_ne
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.det_lead_ne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:56:15.928828+00:00
-- url     : https://prove2.me/theorems/f067cb4a-6784-5817-9a6e-c9ce067ad2ec
-- title:
--   Curv Pf: det lead ne
-- statement:
--   The Curv Pf construction uses the det lead ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LeviFinsetSum.lean#L54-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LeviFinsetSum.lean#L54-L66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetSubMapConj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviFinsetSum
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
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates ReciprocityTheory.AnForm Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.det_lead_ne (U : Matrix (Fin r) (Fin r) ℂ) (hU : ∀ a c : Fin r, c < a → U a c = 0) (hd : U.det ≠ 0)
    {m : ℕ} (hm : m ≤ r) : (U.submatrix (Fin.castLE hm) (Fin.castLE hm)).det ≠ 0 := by sorry

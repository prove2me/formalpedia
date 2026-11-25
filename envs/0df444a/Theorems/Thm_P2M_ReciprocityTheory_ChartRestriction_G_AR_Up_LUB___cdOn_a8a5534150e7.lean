-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB___cdOn_a8a5534150e7
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB___cdOn_a8a5534150e7
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:37.184905+00:00
-- url     : https://prove2.me/theorems/9cc85c97-87a3-5e5b-adf1-934883fc66ac
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up LUB   cd On a8a5534150e7: P2 M Reciprocity Theory Chart Restriction G AR Up LUB   cd On a8a5534150e7
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up LUB   cd On a8a5534150e7 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up LUB   cd On a8a5534150e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LocalUnfoldPfB.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LocalUnfoldPfB.lean#L28-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB___cdOn_a8a5534150e7 : ContDiffOn ℂ ∞ (Φ X b1 D) (Uc X b1 D) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«LUB».«Φ_cdOn» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB___cdOn_a8a5534150e7

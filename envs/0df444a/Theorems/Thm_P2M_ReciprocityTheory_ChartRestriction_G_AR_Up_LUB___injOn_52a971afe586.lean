-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB___injOn_52a971afe586
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB___injOn_52a971afe586
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:53:52.458266+00:00
-- url     : https://prove2.me/theorems/3f622aa3-8c85-5a95-b9ba-81cd676e6184
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up LUB   inj On 52a971afe586: P2 M Reciprocity Theory Chart Restriction G AR Up LUB   inj On 52a971afe586
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up LUB   inj On 52a971afe586 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up LUB   inj On 52a971afe586 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LocalUnfoldPfA.lean#L102-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LocalUnfoldPfA.lean#L102-L128

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfA
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
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB___injOn_52a971afe586 (hx1 : rmul x1' b1 ∈ X.dom) :
    Set.InjOn (Φ X b1 D) {z | cpt X (rmul x1' b1) z ∈ ExtFPf.cell D} := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«LUB».«Φ_injOn» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB___injOn_52a971afe586

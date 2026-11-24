-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_invF_mem__0cc67cfea2e1
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_invF_mem__0cc67cfea2e1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:51.721484+00:00
-- url     : https://prove2.me/theorems/ea2f87e8-b415-4071-8977-7eed1d5d704b
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up MI inv F mem  0cc67cfea2e1: P2 M Reciprocity Theory Chart Restriction G AR Up MI inv F mem  0cc67cfea2e1
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up MI inv F mem  0cc67cfea2e1 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up MI inv F mem  0cc67cfea2e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfI.lean#L206-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfI.lean#L206-L219

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_invF_mem__0cc67cfea2e1 {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : invF X b ∈ Bor X.Ψ r := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«MI».«invF_mem'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_invF_mem__0cc67cfea2e1

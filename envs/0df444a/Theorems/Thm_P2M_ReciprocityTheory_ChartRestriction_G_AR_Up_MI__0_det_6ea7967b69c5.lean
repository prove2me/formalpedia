-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI__0_det_6ea7967b69c5
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI__0_det_6ea7967b69c5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:30:09.566409+00:00
-- url     : https://prove2.me/theorems/12ba3459-3e13-49ea-813e-6dc1114e22a8
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up MI  0 det 6ea7967b69c5: P2 M Reciprocity Theory Chart Restriction G AR Up MI  0 det 6ea7967b69c5
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up MI  0 det 6ea7967b69c5 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up MI  0 det 6ea7967b69c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfI.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfI.lean#L93-L99

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI__0_det_6ea7967b69c5 {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) : (β0 X y τ).det ≠ 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«MI».«β0_det» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI__0_det_6ea7967b69c5

-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_rmul_assoc__b4e3d4f6ddc7
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_rmul_assoc__b4e3d4f6ddc7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:59.117851+00:00
-- url     : https://prove2.me/theorems/0e0f373e-2aba-4865-9609-2ff36f8e48f1
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up MI rmul assoc  b4e3d4f6ddc7: P2 M Reciprocity Theory Chart Restriction G AR Up MI rmul assoc  b4e3d4f6ddc7
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up MI rmul assoc  b4e3d4f6ddc7 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up MI rmul assoc  b4e3d4f6ddc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfK.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfK.lean#L118-L120

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfJ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData Finset
open scoped ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_rmul_assoc__b4e3d4f6ddc7 (x b c : Frame X.Ψ r) : rmul x (rmul b c) = rmul (rmul x b) c := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«MI».«rmul_assoc'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_rmul_assoc__b4e3d4f6ddc7

-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_ae_OmF__9487f78edd9d
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_ae_OmF__9487f78edd9d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:28:40.504148+00:00
-- url     : https://prove2.me/theorems/0ff7357c-f92d-4418-97f2-2016e62550f2
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Fund Set Pf ae Om F  9487f78edd9d: P2 M Reciprocity Theory Chart Restriction G AR Up Fund Set Pf ae Om F  9487f78edd9d
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Fund Set Pf ae Om F  9487f78edd9d construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Fund Set Pf ae Om F  9487f78edd9d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FundSetPf.lean#L199-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FundSetPf.lean#L199-L201

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_Lemmata_GeneralBFactTer_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (x0 : Frame X.Ψ r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_ae_OmF__9487f78edd9d : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«FundSetPf».«ae_OmF'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_ae_OmF__9487f78edd9d

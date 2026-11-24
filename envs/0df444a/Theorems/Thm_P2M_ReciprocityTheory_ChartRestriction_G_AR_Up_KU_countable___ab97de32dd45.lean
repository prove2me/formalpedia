-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_countable___ab97de32dd45
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_countable___ab97de32dd45
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:02:00.145801+00:00
-- url     : https://prove2.me/theorems/24b57299-7fe6-4fd6-af9d-f08834b7649d
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up KU countable   ab97de32dd45: P2 M Reciprocity Theory Chart Restriction G AR Up KU countable   ab97de32dd45
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up KU countable   ab97de32dd45 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up KU countable   ab97de32dd45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPf.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPf.lean#L12-L16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_countable___ab97de32dd45 (X : Data E r) : Countable X.Γ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«KU».«countable_Γ» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_countable___ab97de32dd45

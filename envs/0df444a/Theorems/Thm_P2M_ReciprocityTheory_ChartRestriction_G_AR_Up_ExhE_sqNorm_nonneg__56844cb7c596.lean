-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhE_sqNorm_nonneg__56844cb7c596
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhE_sqNorm_nonneg__56844cb7c596
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:14:18.420996+00:00
-- url     : https://prove2.me/theorems/cf026f77-022e-5ad2-a95f-6d899f481fbf
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Exh E sq Norm nonneg  56844cb7c596: P2 M Reciprocity Theory Chart Restriction G AR Up Exh E sq Norm nonneg  56844cb7c596
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Exh E sq Norm nonneg  56844cb7c596 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Exh E sq Norm nonneg  56844cb7c596 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustStatementPfC.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustStatementPfC.lean#L20-L21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
variable {f p q N' : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhE_sqNorm_nonneg__56844cb7c596 {m : ℕ} (g : Fin m → ℂ) : 0 ≤ sqNorm g := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«ExhE».«sqNorm_nonneg'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhE_sqNorm_nonneg__56844cb7c596

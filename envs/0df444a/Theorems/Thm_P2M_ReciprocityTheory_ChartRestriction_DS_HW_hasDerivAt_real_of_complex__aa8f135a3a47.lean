-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_real_of_complex__aa8f135a3a47
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_real_of_complex__aa8f135a3a47
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:02.990193+00:00
-- url     : https://prove2.me/theorems/5c05583c-b180-476a-96ba-eecbadd290a9
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW has Deriv At real of complex  aa8f135a3a47: P2 M Reciprocity Theory Chart Restriction DS HW has Deriv At real of complex  aa8f135a3a47
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW has Deriv At real of complex  aa8f135a3a47 construction uses the P2 M Reciprocity Theory Chart Restriction DS HW has Deriv At real of complex  aa8f135a3a47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L42-L47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_real_of_complex__aa8f135a3a47 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {g : ℂ → F} {g' : F} {z : ℝ} (h : HasDerivAt g g' (z : ℂ)) :
    HasDerivAt (fun y : ℝ => g (y : ℂ)) g' z := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«hasDerivAt_real_of_complex'» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_real_of_complex__aa8f135a3a47

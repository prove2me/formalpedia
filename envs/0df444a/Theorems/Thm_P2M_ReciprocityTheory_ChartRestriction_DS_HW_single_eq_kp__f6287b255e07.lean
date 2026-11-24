-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_single_eq_kp__f6287b255e07
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_single_eq_kp__f6287b255e07
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:56:44.039983+00:00
-- url     : https://prove2.me/theorems/d1be9ee7-2186-4a42-a40c-2457df5c3ec7
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW single eq kp  f6287b255e07: P2 M Reciprocity Theory Chart Restriction DS HW single eq kp  f6287b255e07
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW single eq kp  f6287b255e07 construction uses the P2 M Reciprocity Theory Chart Restriction DS HW single eq kp  f6287b255e07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L199-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L199-L208

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_single_eq_kp__f6287b255e07 (a b : Fin n) :
    Matrix.single b a (1 : ℂ) = -kp1 a b + Complex.I • kp2 a b := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«single_eq_kp'» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_single_eq_kp__f6287b255e07

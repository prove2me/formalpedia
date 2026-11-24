-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_iff__24a5ac304dfc
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_iff__24a5ac304dfc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:34.432427+00:00
-- url     : https://prove2.me/theorems/0fd2665d-1369-4850-ab66-3c373fc2d88b
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW in K iff  24a5ac304dfc: P2 M Reciprocity Theory Chart Restriction DS HW in K iff  24a5ac304dfc
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW in K iff  24a5ac304dfc construction uses the P2 M Reciprocity Theory Chart Restriction DS HW in K iff  24a5ac304dfc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L18-L31

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_iff__24a5ac304dfc (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inK ε X ↔ Xᴴ = -X ∧ X * Jm ε = Jm ε * X := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«inK_iff'» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_iff__24a5ac304dfc

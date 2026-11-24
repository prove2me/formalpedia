-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_star_d__89a207fa12af
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_star_d__89a207fa12af
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:55:57.45907+00:00
-- url     : https://prove2.me/theorems/4889446d-9cb5-445d-b784-0dc51a935e15
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW KType star d  89a207fa12af: P2 M Reciprocity Theory Chart Restriction DS HW KType star d  89a207fa12af
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW KType star d  89a207fa12af construction uses the P2 M Reciprocity Theory Chart Restriction DS HW KType star d  89a207fa12af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L49-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L49-L68

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_star_d__89a207fa12af {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : star (T.dτ X) = -T.dτ X := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«KType».«star_dτ» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_star_d__89a207fa12af

-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__bracket_single_879de344838e
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__bracket_single_879de344838e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:12:52.656079+00:00
-- url     : https://prove2.me/theorems/2ef8dcf5-b120-4cef-be35-7df8068ee65f
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW KType d  bracket single 879de344838e: P2 M Reciprocity Theory Chart Restriction DS HW KType d  bracket single 879de344838e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW KType d  bracket single 879de344838e construction uses the P2 M Reciprocity Theory Chart Restriction DS HW KType d  bracket single 879de344838e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L237-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L237-L245

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__bracket_single_879de344838e {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    {a b c d : Fin n} (hab : ε a = ε b) (hcd : ε c = ε d) :
    T.dτ (Matrix.single a b 1) * T.dτ (Matrix.single c d 1) -
        T.dτ (Matrix.single c d 1) * T.dτ (Matrix.single a b 1) =
      T.dτ (Matrix.single a b 1 * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«KType».«dτ_bracket_single» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__bracket_single_879de344838e

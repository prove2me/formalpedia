-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_conj_d__50b083afe397
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_conj_d__50b083afe397
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:15:40.091157+00:00
-- url     : https://prove2.me/theorems/e3290726-04d5-5061-9c4b-b0fcecb64411
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW KType conj d  50b083afe397: P2 M Reciprocity Theory Chart Restriction DS HW KType conj d  50b083afe397
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW KType conj d  50b083afe397 construction uses the P2 M Reciprocity Theory Chart Restriction DS HW KType conj d  50b083afe397 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L88-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L88-L122

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_conj_d__50b083afe397 {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    T.op k * T.dτ Y * star (T.op k) = T.dτ (toMK k * Y * star (toMK k)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«KType».«conj_dτ» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_conj_d__50b083afe397

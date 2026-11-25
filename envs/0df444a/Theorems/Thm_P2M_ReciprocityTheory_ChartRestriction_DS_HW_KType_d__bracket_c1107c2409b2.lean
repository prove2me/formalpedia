-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__bracket_c1107c2409b2
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__bracket_c1107c2409b2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:13:41.144414+00:00
-- url     : https://prove2.me/theorems/80b2f2a5-2e08-5375-bc64-6a3679bd17e6
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW KType d  bracket c1107c2409b2: P2 M Reciprocity Theory Chart Restriction DS HW KType d  bracket c1107c2409b2
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW KType d  bracket c1107c2409b2 construction uses the P2 M Reciprocity Theory Chart Restriction DS HW KType d  bracket c1107c2409b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L146-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L146-L173

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__bracket_c1107c2409b2 {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (hY : inK ε Y) :
    T.dτ X * T.dτ Y - T.dτ Y * T.dτ X = T.dτ (X * Y - Y * X) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«KType».«dτ_bracket» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_KType_d__bracket_c1107c2409b2

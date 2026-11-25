-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_kIrrHW_int__ae85b70f4a59
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_kIrrHW_int__ae85b70f4a59
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:11:39.337588+00:00
-- url     : https://prove2.me/theorems/3280c07e-b102-4b4f-b880-2580c584350e
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW k Irr HW int  ae85b70f4a59: P2 M Reciprocity Theory Chart Restriction DS HW k Irr HW int  ae85b70f4a59
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW k Irr HW int  ae85b70f4a59 construction uses the P2 M Reciprocity Theory Chart Restriction DS HW k Irr HW int  ae85b70f4a59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/CompactRelationsApplyComm.lean#L27-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/CompactRelationsApplyComm.lean#L27-L106

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_CompactRelationsApplyComm
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_kIrrHW_int__ae85b70f4a59 (ε : Fin n → Bool) {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F) {Λ : Fin n → ℝ} {V : Submodule ℂ M}
    (hV : IsKIrrHW ε F Λ V) : ∀ a b, a < b → ε a = ε b → ∃ m : ℕ, Λ a - Λ b = m := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«kIrrHW_int'» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_kIrrHW_int__ae85b70f4a59

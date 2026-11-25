-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KRep_op_curve
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.KRep.op_curve
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:47.093977+00:00
-- url     : https://prove2.me/theorems/e7d32c98-71e3-422d-8e33-d5e39263aeb0
-- title:
--   KRep: op curve
-- statement:
--   The KRep construction uses the op curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Stable.lean#L14-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/Stable.lean#L14-L78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Stable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_KType_op_curve

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
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.HW.KRep.op_curve {ε : Fin n → Bool} (R : KRep ε)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (t : ℝ) :
    R.op (γ t) = NormedSpace.exp ((t : ℂ) • R.dτ X) := by sorry

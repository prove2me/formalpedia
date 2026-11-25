-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_tensD_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.tensD_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:57:27.272523+00:00
-- url     : https://prove2.me/theorems/f464bd15-a26d-5f35-9b2a-8f786d40526d
-- title:
--   HW: tens D apply
-- statement:
--   The HW construction uses the tens D apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/TensRepB.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/TensRepB.lean#L57-L60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.ChartRestriction.DS.HW.tensD_apply (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (x : PiLp 2 (fun _ : ι => T.V)) (i : ι) :
    tensD T dρ X x i = T.dτ X (x i) + ∑ j, dρ X i j • x j := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_tensOp_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.tensOp_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:29:06.376278+00:00
-- url     : https://prove2.me/theorems/3f5b09cc-96c8-442e-a32e-0659fb24ab85
-- title:
--   HW: tens Op apply
-- statement:
--   The HW construction uses the tens Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/TensRepA.lean#L128-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/TensRepA.lean#L128-L130

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepA
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
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
  (ρ : KG ε →* unitary (Matrix ι ι ℂ))

theorem ReciprocityTheory.ChartRestriction.DS.HW.tensOp_apply (k : KG ε) (x : PiLp 2 (fun _ : ι => T.V)) (i : ι) :
    tensOp T ρ k x i = ∑ j, ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j • T.op k (x j) := by sorry

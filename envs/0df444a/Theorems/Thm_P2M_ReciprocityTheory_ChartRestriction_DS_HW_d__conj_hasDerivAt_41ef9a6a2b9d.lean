-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_d__conj_hasDerivAt_41ef9a6a2b9d
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_HW_d__conj_hasDerivAt_41ef9a6a2b9d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:50.887844+00:00
-- url     : https://prove2.me/theorems/d0924606-e187-5414-8828-35698b5c4524
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS HW d  conj has Deriv At 41ef9a6a2b9d: P2 M Reciprocity Theory Chart Restriction DS HW d  conj has Deriv At 41ef9a6a2b9d
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS HW d  conj has Deriv At 41ef9a6a2b9d construction uses the P2 M Reciprocity Theory Chart Restriction DS HW d  conj has Deriv At 41ef9a6a2b9d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L136-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean#L136-L142

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
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem P2M_ReciprocityTheory_ChartRestriction_DS_HW_d__conj_hasDerivAt_41ef9a6a2b9d {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun y : ℝ => T.dτ (NormedSpace.exp ((y : ℂ) • X) * Y *
      NormedSpace.exp ((y : ℂ) • (-X)))) (T.dτ (X * Y - Y * X)) 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«HW».«dτ_conj_hasDerivAt» := P2M_ReciprocityTheory_ChartRestriction_DS_HW_d__conj_hasDerivAt_41ef9a6a2b9d

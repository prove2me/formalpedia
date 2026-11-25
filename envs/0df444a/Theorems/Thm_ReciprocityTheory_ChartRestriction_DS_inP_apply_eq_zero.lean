-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inP_apply_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.inP_apply_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:09.324354+00:00
-- url     : https://prove2.me/theorems/e8125975-983b-4d69-8a71-16ac61a39bce
-- title:
--   DS: in P apply eq zero
-- statement:
--   The DS construction uses the in P apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ConjTransposeEqOfInG.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ConjTransposeEqOfInG.lean#L74-L76

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InPApplyEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Theorems.Thm_UpperTheory_Reformulated_B_Qh16_inP_apply_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.inP_apply_eq_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X)
    {a b : Fin n} (hab : ε a = ε b) : X a b = 0 := by sorry

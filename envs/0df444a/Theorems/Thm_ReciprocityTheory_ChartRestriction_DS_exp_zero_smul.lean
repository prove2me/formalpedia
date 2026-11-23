-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exp_zero_smul
-- name    : ReciprocityTheory.ChartRestriction.DS.exp_zero_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:18.265822+00:00
-- url     : https://prove2.me/theorems/721df934-2305-4afc-92d0-5b446c9c3c04
-- title:
--   DS: exp zero smul
-- statement:
--   The DS construction uses the exp zero smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ConjTransposeEqOfInG.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ConjTransposeEqOfInG.lean#L58-L60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InPApplyEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
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

theorem ReciprocityTheory.ChartRestriction.DS.exp_zero_smul (X : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by sorry

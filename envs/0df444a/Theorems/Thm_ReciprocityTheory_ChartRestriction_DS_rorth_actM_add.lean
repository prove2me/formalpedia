-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_actM_add
-- name    : ReciprocityTheory.ChartRestriction.DS.rorth_actM_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:10:11.072067+00:00
-- url     : https://prove2.me/theorems/1e0f4270-ac77-5786-8f57-31dada426d81
-- title:
--   DS: rorth act M add
-- statement:
--   The DS construction uses the rorth act M add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/RorthFunctionalEqZero.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/RorthFunctionalEqZero.lean#L74-L77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.rorth_actM_add {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    actM E (X + Y) = actM E X + actM E Y := by sorry

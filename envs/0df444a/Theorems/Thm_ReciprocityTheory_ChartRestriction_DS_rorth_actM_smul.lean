-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_actM_smul
-- name    : ReciprocityTheory.ChartRestriction.DS.rorth_actM_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:00.842936+00:00
-- url     : https://prove2.me/theorems/d8be2c8e-e954-5081-9cad-79d42e4b58d0
-- title:
--   DS: rorth act M smul
-- statement:
--   The DS construction uses the rorth act M smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/RorthFunctionalEqZero.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/RorthFunctionalEqZero.lean#L79-L82

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

theorem ReciprocityTheory.ChartRestriction.DS.rorth_actM_smul {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    actM E (c • X) = c • actM E X := by sorry

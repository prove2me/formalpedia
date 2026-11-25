-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_inK_comb
-- name    : ReciprocityTheory.ChartRestriction.DS.rorth_inK_comb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:07.289568+00:00
-- url     : https://prove2.me/theorems/7c0a38fb-430a-5314-b12d-b88b312b53ad
-- title:
--   DS: rorth in K comb
-- statement:
--   The DS construction uses the rorth in K comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/RorthFunctionalEqZero.lean#L128-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/RorthFunctionalEqZero.lean#L128-L134

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

theorem ReciprocityTheory.ChartRestriction.DS.rorth_inK_comb {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) (c : ℂ) :
    inK ε (c • Matrix.single a b (1 : ℂ) + (-star c) • Matrix.single b a (1 : ℂ)) := by sorry

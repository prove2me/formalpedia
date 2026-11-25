-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_inK_of_skew
-- name    : ReciprocityTheory.ChartRestriction.DS.rorth_inK_of_skew
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:55:07.57089+00:00
-- url     : https://prove2.me/theorems/aa53d39f-0afe-49b3-8cec-9038c001c50b
-- title:
--   DS: rorth in K of skew
-- statement:
--   The DS construction uses the rorth in K of skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/RorthFunctionalEqZero.lean#L104-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/RorthFunctionalEqZero.lean#L104-L108

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

theorem ReciprocityTheory.ChartRestriction.DS.rorth_inK_of_skew {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (h1 : Zᴴ = -Z)
    (h2 : Z * Jm ε = Jm ε * Z) : inK ε Z := by sorry

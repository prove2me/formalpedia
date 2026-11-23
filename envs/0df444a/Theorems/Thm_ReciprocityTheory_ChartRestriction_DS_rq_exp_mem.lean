-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_exp_mem
-- name    : ReciprocityTheory.ChartRestriction.DS.rq_exp_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:12:02.633713+00:00
-- url     : https://prove2.me/theorems/7eacf7e2-0241-479f-8f97-0714d3281a6a
-- title:
--   DS: rq exp mem
-- statement:
--   The DS construction uses the rq exp mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IsInLieAlgebraISmulAddConjTranspose.lean#L84-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IsInLieAlgebraISmulAddConjTranspose.lean#L84-L102

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
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

theorem ReciprocityTheory.ChartRestriction.DS.rq_exp_mem (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inG ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := by sorry

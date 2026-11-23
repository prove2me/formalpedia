-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_inG_S
-- name    : ReciprocityTheory.ChartRestriction.DS.rq_inG_S
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:26.859106+00:00
-- url     : https://prove2.me/theorems/e5eb9a6a-b321-476e-9589-835395200f7c
-- title:
--   DS: rq in G S
-- statement:
--   The DS construction uses the rq in G S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IsInLieAlgebraISmulAddConjTranspose.lean#L142-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IsInLieAlgebraISmulAddConjTranspose.lean#L142-L150

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

theorem ReciprocityTheory.ChartRestriction.DS.rq_inG_S (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (X - Jm ε * Xᴴ * Jm ε) := by sorry

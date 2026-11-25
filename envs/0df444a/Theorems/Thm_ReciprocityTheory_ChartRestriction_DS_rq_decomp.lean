-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rq_decomp
-- name    : ReciprocityTheory.ChartRestriction.DS.rq_decomp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:56:43.263862+00:00
-- url     : https://prove2.me/theorems/30121222-f6d8-5864-bf02-7050c0f72daa
-- title:
--   DS: rq decomp
-- statement:
--   The DS construction uses the rq decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IsInLieAlgebraISmulAddConjTranspose.lean#L162-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/IsInLieAlgebraISmulAddConjTranspose.lean#L162-L169

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

theorem ReciprocityTheory.ChartRestriction.DS.rq_decomp (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    (1 / 2 : ℂ) • (X - Jm ε * Xᴴ * Jm ε) + (-(Complex.I / 2)) • (Complex.I • (X + Jm ε * Xᴴ * Jm ε))
      = X := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_sop_comp
-- name    : ReciprocityTheory.ChartRestriction.DS.USum.sop_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:45:35.936259+00:00
-- url     : https://prove2.me/theorems/a515a745-1276-43cb-81b2-02a8c074a66a
-- title:
--   USum: sop comp
-- statement:
--   The USum construction uses the sop comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L37-L39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix WithLp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.USum
variable {n : ℕ}
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

theorem ReciprocityTheory.ChartRestriction.DS.USum.sop_comp (A A' : H₁ →L[ℂ] H₁) (B B' : H₂ →L[ℂ] H₂) :
    sop (A.comp A') (B.comp B') = (sop A B).comp (sop A' B') := by sorry

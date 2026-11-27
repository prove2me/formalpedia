-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lf_rhoHol_sub_rhoN
-- name    : ReciprocityTheory.ChartRestriction.DS.lf_rhoHol_sub_rhoN
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:10:59.834133+00:00
-- url     : https://prove2.me/theorems/1b9b53f3-daf0-53ad-8423-02060c53413e
-- title:
--   DS: lf rho Hol sub rho N
-- statement:
--   The DS construction uses the lf rho Hol sub rho N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockC.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockC.lean#L19-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockC
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.lf_rhoHol_sub_rhoN (ε : Fin n → Bool) (c : Fin n) :
    (rhoHol ε - rhoN ε) c = if ε c = true then ((univ.filter fun a => ε a = false ∧ a < c).card : ℝ)
      else -((univ.filter fun i => ε i = true ∧ c < i).card : ℝ) := by sorry

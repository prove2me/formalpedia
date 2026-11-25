-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fock_contractLeft_involute
-- name    : ReciprocityTheory.ChartRestriction.DS.fock_contractLeft_involute
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:32.534395+00:00
-- url     : https://prove2.me/theorems/5e5a992a-79d3-4b19-9cb0-ac0a1137f0c9
-- title:
--   DS: fock contract Left involute
-- statement:
--   The DS construction uses the fock contract Left involute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/FockTA.lean#L80-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/FockTA.lean#L80-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
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

theorem ReciprocityTheory.ChartRestriction.DS.fock_contractLeft_involute (d : Module.Dual ℂ (Fin n × Fin n → ℂ)) (x : Fock n) :
    CliffordAlgebra.contractLeft d (CliffordAlgebra.involute x) =
      -CliffordAlgebra.involute (CliffordAlgebra.contractLeft d x) := by sorry

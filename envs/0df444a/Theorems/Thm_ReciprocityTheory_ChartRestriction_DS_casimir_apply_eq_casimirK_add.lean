-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimir_apply_eq_casimirK_add
-- name    : ReciprocityTheory.ChartRestriction.DS.casimir_apply_eq_casimirK_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:49:33.824126+00:00
-- url     : https://prove2.me/theorems/22075720-15e6-408a-8d23-4bc3ada8198b
-- title:
--   DS: casimir apply eq casimir K add
-- statement:
--   The DS construction uses the casimir apply eq casimir K add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/NcBound.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/NcBound.lean#L16-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_WeightBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_NcBound
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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.casimir_apply_eq_casimirK_add (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (x : M) :
    casimir E x = casimirK ε E x +
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), E a b (E b a x) := by sorry

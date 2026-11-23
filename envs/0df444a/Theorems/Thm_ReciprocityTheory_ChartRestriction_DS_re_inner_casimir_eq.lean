-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_re_inner_casimir_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.re_inner_casimir_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:26.42547+00:00
-- url     : https://prove2.me/theorems/4a460b5a-790b-43ea-b16a-699e60747efb
-- title:
--   DS: re inner casimir eq
-- statement:
--   The DS construction uses the re inner casimir eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/NcBound.lean#L37-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/NcBound.lean#L37-L52

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

theorem ReciprocityTheory.ChartRestriction.DS.re_inner_casimir_eq (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hU : IsInfUnitary ε E) (x : M) :
    RCLike.re (inner ℂ (casimir E x) x) = RCLike.re (inner ℂ (casimirK ε E x) x) -
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_commutator
-- name    : ReciprocityTheory.ChartRestriction.DS.factorAd_commutator
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:33.901545+00:00
-- url     : https://prove2.me/theorems/a422763a-e640-4f25-8efb-db789711436d
-- title:
--   DS: factor Ad commutator
-- statement:
--   The DS construction uses the factor Ad commutator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L77-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean#L77-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
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
variable {E : Fin n → Fin n → Module.End ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.factorAd_commutator (k : ℕ) (i : Fin k) (a b c d : Fin n) :
    factorAd (M := M) k i a b * factorAd k i c d - factorAd k i c d * factorAd k i a b =
      (if b = c then factorAd k i a d else 0) - (if d = a then factorAd k i c b else 0) := by sorry

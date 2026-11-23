-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_crossOp_khw
-- name    : ReciprocityTheory.ChartRestriction.DS.crossOp_khw
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:02:20.038842+00:00
-- url     : https://prove2.me/theorems/abff01dd-8e4c-4959-817a-13fd85f3da32
-- title:
--   DS: cross Op khw
-- statement:
--   The DS construction uses the cross Op khw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/InnerCrossOpEigEqZero.lean#L105-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/InnerCrossOpEigEqZero.lean#L105-L126

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Weights
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_InnerCrossOpEigEqZero
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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.crossOp_khw (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) {x : Big n 1 M} (hx : x ∈ ncV ε V 1) (hx0 : x ≠ 0)
    {ν : Fin n → ℝ} (hν : IsKHWVec ε (bAct E 1) ν x) :
    ∃ r s : Fin n, ε r ≠ ε s ∧ ν = lowK ε lam + root r s ∧
      (2 : ℂ) • crossOp ε E 1 0 x =
        ((casValK ε ν - n - casValK ε (lowK ε lam) : ℝ) : ℂ) • x := by sorry

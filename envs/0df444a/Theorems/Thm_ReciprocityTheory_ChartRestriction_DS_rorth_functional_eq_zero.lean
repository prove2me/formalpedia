-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_functional_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.rorth_functional_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:01.076234+00:00
-- url     : https://prove2.me/theorems/c854ae71-e32f-49e0-b0ad-844721601c39
-- title:
--   DS: rorth functional eq zero
-- statement:
--   The DS construction uses the rorth functional eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/RorthFunctionalEqZero.lean#L29-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/RorthFunctionalEqZero.lean#L29-L68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero
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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.rorth_functional_eq_zero (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) (f : M →ₗ[ℂ] ℂ) (hfV : ∀ v ∈ V, f v = 0)
    (hfd : ∀ a y, f (E a a y) = (lowK ε lam a : ℂ) * f y)
    (hfl : ∀ a b, a < b → ε a = ε b → ∀ y, f (E b a y) = 0) :
    ∀ y ∈ genSub E V, f y = 0 := by sorry

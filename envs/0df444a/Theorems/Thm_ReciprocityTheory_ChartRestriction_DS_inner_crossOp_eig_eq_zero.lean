-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inner_crossOp_eig_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.inner_crossOp_eig_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:39.673087+00:00
-- url     : https://prove2.me/theorems/0e763ed4-1786-4ee4-b144-07a2f0b76d81
-- title:
--   DS: inner cross Op eig eq zero
-- statement:
--   The DS construction uses the inner cross Op eig eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/InnerCrossOpEigEqZero.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/InnerCrossOpEigEqZero.lean#L23-L30

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

theorem ReciprocityTheory.ChartRestriction.DS.inner_crossOp_eig_eq_zero (hU : IsInfUnitary ε E) {θ θ' : ℝ} (hθ : θ ≠ θ')
    {u v : Big n 1 M} (hu : crossOp ε E 1 0 u = (θ : ℂ) • u)
    (hv : crossOp ε E 1 0 v = (θ' : ℂ) • v) : inner ℂ u v = 0 := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Wm_perp_Wp
-- name    : ReciprocityTheory.ChartRestriction.DS.Wm_perp_Wp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:08:00.238668+00:00
-- url     : https://prove2.me/theorems/d301c279-a9f9-41b1-9bef-d20e2c0daa3b
-- title:
--   DS: Wm perp Wp
-- statement:
--   The DS construction uses the Wm perp Wp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/InnerCrossOpEigEqZero.lean#L32-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/InnerCrossOpEigEqZero.lean#L32-L42

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

theorem ReciprocityTheory.ChartRestriction.DS.Wm_perp_Wp (hU : IsInfUnitary ε E) {x y : Big n 1 M} (hx : x ∈ Wm ε E V)
    (hy : y ∈ Wp ε E V) : inner ℂ x y = 0 := by sorry

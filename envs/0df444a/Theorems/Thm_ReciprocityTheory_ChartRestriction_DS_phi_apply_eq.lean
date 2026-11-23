-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_apply_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.phi_apply_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:33.279469+00:00
-- url     : https://prove2.me/theorems/538bd287-6646-4f90-ac94-0a1f93834e7b
-- title:
--   DS: phi apply eq
-- statement:
--   The DS construction uses the phi apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L25-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
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
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.phi_apply_eq (k : ℕ) (F : Big n k M) : phi E k F = ∑ κ, word E κ (F κ) := by sorry

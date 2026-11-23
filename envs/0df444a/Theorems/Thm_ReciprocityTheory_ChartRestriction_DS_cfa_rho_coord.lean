-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_cfa_rho_coord
-- name    : ReciprocityTheory.ChartRestriction.DS.cfa_rho_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:55:13.939811+00:00
-- url     : https://prove2.me/theorems/1bf1a6c0-8412-4408-b7af-e957815233f0
-- title:
--   DS: cfa rho coord
-- statement:
--   The DS construction uses the cfa rho coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean#L132-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean#L132-L156

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
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

theorem ReciprocityTheory.ChartRestriction.DS.cfa_rho_coord (ε : Fin n → Bool) (c : Fin n) :
    (rhoHol ε - rhoN ε) c = ∑ b, ((if ε c = true ∧ ε b = false ∧ b < c then (1 : ℝ) else 0) -
      (if ε b = true ∧ ε c = false ∧ c < b then (1 : ℝ) else 0)) := by sorry

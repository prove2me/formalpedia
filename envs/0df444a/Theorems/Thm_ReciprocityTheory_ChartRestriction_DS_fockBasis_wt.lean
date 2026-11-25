-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fockBasis_wt
-- name    : ReciprocityTheory.ChartRestriction.DS.fockBasis_wt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:00.100669+00:00
-- url     : https://prove2.me/theorems/ea485ef8-55d4-4005-a0ae-47c4c46b3101
-- title:
--   DS: fock Basis wt
-- statement:
--   The DS construction uses the fock Basis wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean#L117-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean#L117-L130

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

theorem ReciprocityTheory.ChartRestriction.DS.fockBasis_wt (ε : Fin n → Bool) (s : Finset (Fin (n * n))) (c : Fin n) :
    sgE ε cpFock cmFock c c (fockBasis n s) = ((fockWt ε s c : ℝ) : ℂ) • fockBasis n s := by sorry

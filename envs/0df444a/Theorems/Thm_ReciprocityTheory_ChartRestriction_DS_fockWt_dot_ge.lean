-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fockWt_dot_ge
-- name    : ReciprocityTheory.ChartRestriction.DS.fockWt_dot_ge
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:51:37.543297+00:00
-- url     : https://prove2.me/theorems/1a32ff81-6544-4733-96f3-1cda4083e7dd
-- title:
--   DS: fock Wt dot ge
-- statement:
--   The DS construction uses the fock Wt dot ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean#L162-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean#L162-L201

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

theorem ReciprocityTheory.ChartRestriction.DS.fockWt_dot_ge (ε : Fin n → Bool) {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    (s : Finset (Fin (n * n))) : dot (rhoHol ε - rhoN ε) lam ≤ dot (fockWt ε s) lam := by sorry

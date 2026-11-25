-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sgE_one
-- name    : ReciprocityTheory.ChartRestriction.DS.sgE_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:54.197034+00:00
-- url     : https://prove2.me/theorems/eb86783a-37a8-59b8-8da1-9c5f2d6a207c
-- title:
--   DS: sg E one
-- statement:
--   The DS construction uses the sg E one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeA.lean#L78-L80

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

theorem ReciprocityTheory.ChartRestriction.DS.sgE_one (ε : Fin n → Bool) (c : Fin n) : sgE ε cpFock cmFock c c (1 : Fock n) = 0 := by sorry

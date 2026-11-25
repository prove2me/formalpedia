-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfa_basis_list
-- name    : ReciprocityTheory.ChartRestriction.DS.lfa_basis_list
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:54:38.463054+00:00
-- url     : https://prove2.me/theorems/3a0d0987-56ce-55be-9ca5-dc59f1169a29
-- title:
--   DS: lfa basis list
-- statement:
--   The DS construction uses the lfa basis list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L30-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
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

theorem ReciprocityTheory.ChartRestriction.DS.lfa_basis_list (S : Finset (Fin (n * n))) :
    fockBasis n S = ((List.ofFn fun i => finProdFinEquiv.symm (S.orderEmbOfFin rfl i)).map
      fun y => ExteriorAlgebra.ι ℂ (Pi.single y (1 : ℂ))).prod := by sorry

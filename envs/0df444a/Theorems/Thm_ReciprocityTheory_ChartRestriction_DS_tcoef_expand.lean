-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_expand
-- name    : ReciprocityTheory.ChartRestriction.DS.tcoef_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:44.591799+00:00
-- url     : https://prove2.me/theorems/ec77d19d-9fc2-44d1-ab62-7270fdfd7f82
-- title:
--   DS: tcoef expand
-- statement:
--   The DS construction uses the tcoef expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L40-L49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.tcoef_expand (y : TensorProduct ℂ M (Fock n)) :
    y = ∑ s, tcoef ((fockBasis n).coord s) y ⊗ₜ fockBasis n s := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_lTensor
-- name    : ReciprocityTheory.ChartRestriction.DS.tcoef_lTensor
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:57.403134+00:00
-- url     : https://prove2.me/theorems/f6fd90e4-93df-566c-bacb-4515a84f8300
-- title:
--   DS: tcoef l Tensor
-- statement:
--   The DS construction uses the tcoef l Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L26-L31

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

theorem ReciprocityTheory.ChartRestriction.DS.tcoef_lTensor (φ : Module.Dual ℂ (Fock n)) (S : Module.End ℂ (Fock n))
    (y : TensorProduct ℂ M (Fock n)) : tcoef φ (LinearMap.lTensor M S y) = tcoef (φ ∘ₗ S) y := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lf_sgE_tensor
-- name    : ReciprocityTheory.ChartRestriction.DS.lf_sgE_tensor
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:38.208152+00:00
-- url     : https://prove2.me/theorems/1b5883e9-15e4-55bf-85f1-ccd0fcf861e1
-- title:
--   DS: lf sg E tensor
-- statement:
--   The DS construction uses the lf sg E tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockE.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockE.lean#L13-L28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockE
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
variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem ReciprocityTheory.ChartRestriction.DS.lf_sgE_tensor (ε : Fin n → Bool) (a b : Fin n) :
    sgE ε (cpT (N := N) (n := n)) cmT a b = TensorProduct.map LinearMap.id (sgE ε cpFock cmFock a b) := by sorry

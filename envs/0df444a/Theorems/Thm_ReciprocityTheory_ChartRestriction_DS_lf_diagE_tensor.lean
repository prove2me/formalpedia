-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lf_diagE_tensor
-- name    : ReciprocityTheory.ChartRestriction.DS.lf_diagE_tensor
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:24.107665+00:00
-- url     : https://prove2.me/theorems/a70eb396-abfc-540e-a935-29e234105d72
-- title:
--   DS: lf diag E tensor
-- statement:
--   The DS construction uses the lf diag E tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockE.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockE.lean#L30-L35

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

theorem ReciprocityTheory.ChartRestriction.DS.lf_diagE_tensor (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) :
    diagE ε (eT E) cpT cmT a b =
      TensorProduct.map (E a b) LinearMap.id + TensorProduct.map LinearMap.id (sgE ε cpFock cmFock a b) := by sorry

-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfLift_diagE
-- name    : ReciprocityTheory.ChartRestriction.DS.lfLift_diagE
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:15.693356+00:00
-- url     : https://prove2.me/theorems/108a8e01-de0a-5056-b547-ff6f17bfbe20
-- title:
--   DS: lf Lift diag E
-- statement:
--   The DS construction uses the lf Lift diag E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockE.lean#L74-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockE.lean#L74-L85

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

theorem ReciprocityTheory.ChartRestriction.DS.lfLift_diagE (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n)
    (x : LfIdx ε → N) :
    diagE ε (eT E) cpT cmT a b (lfLift ε x) =
      lfLift ε (fun T => E a b (x T) + ∑ S, lfMat ε a b T S • x S) := by sorry

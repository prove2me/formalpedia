-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfLift_tcoef
-- name    : ReciprocityTheory.ChartRestriction.DS.lfLift_tcoef
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:59:30.103144+00:00
-- url     : https://prove2.me/theorems/7baaf670-c1bb-456d-9e2f-d44e5de58bcf
-- title:
--   DS: lf Lift tcoef
-- statement:
--   The DS construction uses the lf Lift tcoef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockE.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockE.lean#L58-L64

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

theorem ReciprocityTheory.ChartRestriction.DS.lfLift_tcoef (ε : Fin n → Bool) (x : LfIdx ε → N) (S : LfIdx ε) :
    tcoef ((fockBasis n).coord S.1) (lfLift ε x) = x S := by sorry

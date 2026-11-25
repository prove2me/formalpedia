-- Prove2me | Theorems.Thm_PI_tensCpctDen_of
-- name    : PI.tensCpctDen_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:46:50.585161+00:00
-- url     : https://prove2.me/theorems/7d40f550-1eb2-422a-bf04-8c0dfa2eb234
-- title:
--   PI: tens Cpct Den of
-- statement:
--   The PI construction uses the tens Cpct Den of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactTensorDensity/TensCpctDenOf.lean#L49-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactTensorDensity/TensCpctDenOf.lean#L49-L99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactTensorDensity_TensCpctDenOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct PI.TensCpctDenWork

theorem PI.tensCpctDen_of (hA : PI.AdCpctDen) : PI.TensCpctDen := by sorry

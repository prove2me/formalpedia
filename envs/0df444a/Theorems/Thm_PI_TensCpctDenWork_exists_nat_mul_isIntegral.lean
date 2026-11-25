-- Prove2me | Theorems.Thm_PI_TensCpctDenWork_exists_nat_mul_isIntegral
-- name    : PI.TensCpctDenWork.exists_nat_mul_isIntegral
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:47.703866+00:00
-- url     : https://prove2.me/theorems/d15adbd9-d564-57db-9883-3486d2a93fc0
-- title:
--   Tens Cpct Den Work: exists nat mul is Integral
-- statement:
--   The Tens Cpct Den Work construction uses the exists nat mul is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactTensorDensity/TensCpctDenOf.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactTensorDensity/TensCpctDenOf.lean#L41-L44

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
open PI PI.TensCpctDenWork
open NumberField IsDedekindDomain TensorProduct

theorem PI.TensCpctDenWork.exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ D : ℕ, 0 < D ∧ IsIntegral ℤ ((D : E) * x) := by sorry

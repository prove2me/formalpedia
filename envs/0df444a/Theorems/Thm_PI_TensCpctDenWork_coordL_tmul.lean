-- Prove2me | Theorems.Thm_PI_TensCpctDenWork_coordL_tmul
-- name    : PI.TensCpctDenWork.coordL_tmul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:53.962857+00:00
-- url     : https://prove2.me/theorems/5e9f9d35-a517-4cae-860c-fb18712ee135
-- title:
--   Tens Cpct Den Work: coord L tmul
-- statement:
--   The Tens Cpct Den Work construction uses the coord L tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactTensorDensity/TensCpctDenOf.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactTensorDensity/TensCpctDenOf.lean#L36-L37

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
variable {F E R : Type} [Field F] [CommRing E] [Algebra F E] [CommRing R] [Algebra F R]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem PI.TensCpctDenWork.coordL_tmul (φ : E →ₗ[F] F) (e : E) (x : R) : coordL φ (e ⊗ₜ[F] x) = φ e • x := by sorry

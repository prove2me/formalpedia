-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_nsmul_tmul_F
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.nsmul_tmul_F
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:09:19.832712+00:00
-- url     : https://prove2.me/theorems/07ed42ec-7243-4696-8a16-29e2b8f8d5d8
-- title:
--   UJClass Fin: nsmul tmul F
-- statement:
--   The UJClass Fin construction uses the nsmul tmul F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/RationalPointsDense.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/RationalPointsDense.lean#L22-L27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

theorem PI.UnitaryGroupMassFormula.UJClassFin.nsmul_tmul_F (N : ℕ) (a : Af F) (e : E) : N • (a ⊗ₜ[F] e) = a ⊗ₜ[F] ((N : F) • e) := by sorry

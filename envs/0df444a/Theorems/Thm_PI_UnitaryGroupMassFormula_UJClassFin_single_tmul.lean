-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_single_tmul
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.single_tmul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:38.343879+00:00
-- url     : https://prove2.me/theorems/7a11b2c9-4fb3-47c4-ba19-f1c518ccb0f5
-- title:
--   UJClass Fin: single tmul
-- statement:
--   The UJClass Fin construction uses the single tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/RationalPointsDense.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/RationalPointsDense.lean#L14-L20

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

theorem PI.UnitaryGroupMassFormula.UJClassFin.single_tmul (l : Fin M) (a : Af F) (t : E) :
    Pi.single l (a ⊗ₜ[F] t) = fun i => a ⊗ₜ[F] ((Pi.single l t : Fin M → E) i) := by sorry

-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_latHat_smul
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.latHat_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:06:47.949805+00:00
-- url     : https://prove2.me/theorems/4bbfe39b-e24b-4a98-a6ff-85d70ba7aef9
-- title:
--   UJClass Fin: lat Hat smul
-- statement:
--   The UJClass Fin construction uses the lat Hat smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/RationalPointsDense.lean#L34-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/RationalPointsDense.lean#L34-L51

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

theorem PI.UnitaryGroupMassFormula.UJClassFin.latHat_smul (L : Set (Fin M → E)) {a : Af F} (ha : a ∈ intAf F) {y : Fin M → Af F ⊗[F] E}
    (hy : y ∈ latHat F E L) : (a ⊗ₜ[F] (1 : E)) • y ∈ latHat F E L := by sorry

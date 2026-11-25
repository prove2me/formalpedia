-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_tmul_one_smul_smul
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.tmul_one_smul_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:16:00.873051+00:00
-- url     : https://prove2.me/theorems/e5ab8569-eb47-40ff-96e0-c35fa952170f
-- title:
--   UJClass Mass: tmul one smul smul
-- statement:
--   The UJClass Mass construction uses the tmul one smul smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/AlgebraMapIntIntAf.lean#L129-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/AlgebraMapIntIntAf.lean#L129-L131

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] {M : ℕ}

theorem PI.UnitaryGroupMassFormula.UJClassMass.tmul_one_smul_smul (a a' : Af F) (Y : Fin M → Af F ⊗[F] E) :
    (a ⊗ₜ[F] (1 : E)) • ((a' ⊗ₜ[F] (1 : E)) • Y) = ((a * a') ⊗ₜ[F] (1 : E)) • Y := by sorry

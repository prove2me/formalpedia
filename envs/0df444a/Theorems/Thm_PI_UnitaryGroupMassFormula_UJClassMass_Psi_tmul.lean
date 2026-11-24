-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Psi_tmul
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.Psi_tmul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:27:45.903429+00:00
-- url     : https://prove2.me/theorems/b98d8808-008f-4c9c-9d0e-5013ecf899e2
-- title:
--   UJClass Mass: Psi tmul
-- statement:
--   The UJClass Mass construction uses the Psi tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/OneSubEvTInvInt.lean#L140-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/OneSubEvTInvInt.lean#L140-L141

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct RestrictedProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))

theorem PI.UnitaryGroupMassFormula.UJClassMass.Psi_tmul (a : Af F) (e : E) : Psi (E := E) v (a ⊗ₜ[F] e) = e ⊗ₜ[F] a v := by sorry

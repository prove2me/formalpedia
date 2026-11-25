-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Phi_mul
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.Phi_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:50:58.551975+00:00
-- url     : https://prove2.me/theorems/40c99551-49b2-4e37-a91d-556207c654ba
-- title:
--   UJClass Mass: Phi mul
-- statement:
--   The UJClass Mass construction uses the Phi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/OneSubEvTInvInt.lean#L156-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/OneSubEvTInvInt.lean#L156-L166

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.Phi_mul (x y : E ⊗[F] Fv F v) : Phi v (x * y) = Phi v x * Phi v y := by sorry

-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_af_zero_apply
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.af_zero_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:27.010813+00:00
-- url     : https://prove2.me/theorems/b5afc7f0-aca0-4003-870c-8de0e2a2ab4d
-- title:
--   UJClass Mass: af zero apply
-- statement:
--   The UJClass Mass construction uses the af zero apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/OneSubEvTInvInt.lean#L23-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/OneSubEvTInvInt.lean#L23-L23

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
open Classical
variable {F : Type} [Field F] [NumberField F]

theorem PI.UnitaryGroupMassFormula.UJClassMass.af_zero_apply (w : HeightOneSpectrum (𝓞 F)) : (0 : Af F) w = 0 := by sorry

-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_sgl_one_mul
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.sgl_one_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:14:35.253871+00:00
-- url     : https://prove2.me/theorems/7d08c5d1-f242-4db4-b6af-f527645ae38a
-- title:
--   UJClass Mass: sgl one mul
-- statement:
--   The UJClass Mass construction uses the sgl one mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/OneSubEvTInvInt.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/OneSubEvTInvInt.lean#L62-L66

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
variable (v : HeightOneSpectrum (𝓞 F))

theorem PI.UnitaryGroupMassFormula.UJClassMass.sgl_one_mul (a : Af F) : sgl v 1 * a = sgl v (a v) := by sorry

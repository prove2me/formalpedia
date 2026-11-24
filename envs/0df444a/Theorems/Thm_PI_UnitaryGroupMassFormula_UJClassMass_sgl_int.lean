-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_sgl_int
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.sgl_int
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:51:23.014827+00:00
-- url     : https://prove2.me/theorems/f9ed5b06-4519-40a2-ac5b-acbf56129841
-- title:
--   UJClass Mass: sgl int
-- statement:
--   The UJClass Mass construction uses the sgl int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/OneSubEvTInvInt.lean#L54-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/OneSubEvTInvInt.lean#L54-L60

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.sgl_int {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) : sgl v x ∈ intAf F := by sorry

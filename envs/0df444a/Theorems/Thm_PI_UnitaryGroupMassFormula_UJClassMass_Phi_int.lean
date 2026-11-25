-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Phi_int
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.Phi_int
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:46:08.229846+00:00
-- url     : https://prove2.me/theorems/7246feaa-0232-4299-ad9a-4f7b7b26f79b
-- title:
--   UJClass Mass: Phi int
-- statement:
--   The UJClass Mass construction uses the Phi int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/OneSubEvTInvInt.lean#L172-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/OneSubEvTInvInt.lean#L172-L189

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.Phi_int {s : E ⊗[F] Fv F v}
    (hs : s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (Fv F v) (PI.UnitaryApproxDefs.intOE E) (v.adicCompletionIntegers F).toSubring) :
    Phi v s ∈ Oh F E := by sorry

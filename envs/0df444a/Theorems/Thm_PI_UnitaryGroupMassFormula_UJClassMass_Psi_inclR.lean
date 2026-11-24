-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Psi_inclR
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.Psi_inclR
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:51:16.162422+00:00
-- url     : https://prove2.me/theorems/47f3712f-0ac6-4f47-92ce-c82831a321bf
-- title:
--   UJClass Mass: Psi incl R
-- statement:
--   The UJClass Mass construction uses the Psi incl R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PsiInclR.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PsiInclR.lean#L26-L29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PsiInclR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem PI.UnitaryGroupMassFormula.UJClassMass.Psi_inclR (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    Psi v (inclR (F := F) (Af F) e) = PI.UnitaryApproxDefs.inclE (F := F) (Fv F v) e := by sorry

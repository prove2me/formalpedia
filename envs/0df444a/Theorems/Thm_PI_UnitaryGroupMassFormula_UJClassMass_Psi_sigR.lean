-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Psi_sigR
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.Psi_sigR
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:49:37.369272+00:00
-- url     : https://prove2.me/theorems/f4905bbc-375c-5a34-8add-f7605849eb80
-- title:
--   UJClass Mass: Psi sig R
-- statement:
--   The UJClass Mass construction uses the Psi sig R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PsiInclR.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PsiInclR.lean#L16-L24

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.Psi_sigR (v : HeightOneSpectrum (𝓞 F)) (x : Af F ⊗[F] E) :
    Psi v (PI.UJClassFin.sigR (Af F) σ x) = PI.UnitaryApproxDefs.sigR σ (Fv F v) (Psi v x) := by sorry

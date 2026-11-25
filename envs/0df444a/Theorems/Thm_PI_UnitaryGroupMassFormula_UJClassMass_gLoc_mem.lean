-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_gLoc_mem
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.gLoc_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:43:49.073412+00:00
-- url     : https://prove2.me/theorems/1dfa19a9-78d8-4ea4-942e-a99f90a4b759
-- title:
--   UJClass Mass: g Loc mem
-- statement:
--   The UJClass Mass construction uses the g Loc mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PsiInclR.lean#L43-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PsiInclR.lean#L43-L58

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.gLoc_mem (g : HA (AF F) σ J) (v : HeightOneSpectrum (𝓞 F)) :
    gLoc σ J g v ∈ PI.UnitaryApproxDefs.UPts σ J (Fv F v) := by sorry

-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Lam_mul_sfin
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.Lam_mul_sfin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:01.516196+00:00
-- url     : https://prove2.me/theorems/d21f42dd-4d4e-488b-a4dc-2a9cefdcb1f3
-- title:
--   UJClass Mass: Lam mul sfin
-- statement:
--   The UJClass Mass construction uses the Lam mul sfin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/EquivFunLinOf.lean#L35-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/EquivFunLinOf.lean#L35-L48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.UnitaryGroupMassFormula.UJClassMass.Lam_mul_sfin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E))
    (g : HA (AF F) σ J) (k : SFin σ J L) :
    PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J L (g * k) = PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J L g := by sorry

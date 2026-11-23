-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_emb_ratU
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.emb_ratU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:48:20.069053+00:00
-- url     : https://prove2.me/theorems/b8ed9a4f-a9fb-428f-b003-03607ceeda8b
-- title:
--   UJClass Mass: emb rat U
-- statement:
--   The UJClass Mass construction uses the emb rat U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/EquivFunLinOf.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/EquivFunLinOf.lean#L31-L33

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.emb_ratU (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : GamG σ J) :
    PI.UnitaryGroupMassFormula.UJClassFin.emb σ J (ratU σ J γ) = (γ : HA (AF F) σ J) := by sorry

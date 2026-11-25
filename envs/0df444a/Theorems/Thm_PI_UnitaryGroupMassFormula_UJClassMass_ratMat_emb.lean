-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_ratMat_emb
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.ratMat_emb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:02:41.116603+00:00
-- url     : https://prove2.me/theorems/8a07d7d0-915d-567a-b27d-7b67b6db10d4
-- title:
--   UJClass Mass: rat Mat emb
-- statement:
--   The UJClass Mass construction uses the rat Mat emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean#L45-L47

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_emb_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.UnitaryGroupMassFormula.UJClassMass.ratMat_emb (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (U : UJ (σ : E →+* E) J) :
    ratMat σ J ⟨PI.UnitaryGroupMassFormula.UJClassFin.emb σ J U, PI.UnitaryGroupMassFormula.UJClassFin.emb_mem σ J U⟩ = U := by sorry

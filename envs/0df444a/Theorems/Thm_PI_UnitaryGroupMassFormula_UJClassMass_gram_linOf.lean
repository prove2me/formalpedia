-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_gram_linOf
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.gram_linOf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:02:37.341975+00:00
-- url     : https://prove2.me/theorems/5c387b2b-a936-4c2c-ad22-ad61cfb65c3e
-- title:
--   UJClass Mass: gram lin Of
-- statement:
--   The UJClass Mass construction uses the gram lin Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean#L84-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean#L84-L94

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
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
variable {E V : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V]

theorem PI.UnitaryGroupMassFormula.UJClassMass.gram_linOf {F : Type} [Field F] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (h : V →ₗ⋆[E] V →ₗ[E] E) {M : ℕ} (b : Module.Basis (Fin M) E V) (U : GL (Fin M) E) (i j : Fin M) :
    h (linOf b U (b i)) (linOf b U (b j)) =
      (cT (σ : E →+* E) (U : Matrix (Fin M) (Fin M) E) * gramOf h b * (U : Matrix (Fin M) (Fin M) E)) i j := by sorry

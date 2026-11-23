-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_matGL_mem
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.matGL_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:22.990863+00:00
-- url     : https://prove2.me/theorems/073441ae-5c91-4f1a-9e56-edf0b68d42a8
-- title:
--   UJClass Mass: mat GL mem
-- statement:
--   The UJClass Mass construction uses the mat GL mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean#L96-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean#L96-L103

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.matGL_mem {F : Type} [Field F] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (h : V →ₗ⋆[E] V →ₗ[E] E) {M : ℕ} (b : Module.Basis (Fin M) E V) {u : V ≃ₗ[E] V} (hu : u ∈ isom h) :
    matGL b u ∈ UJ (σ : E →+* E) (gramOf h b) := by sorry

-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_stabT
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.stabT
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:04:48.80185+00:00
-- url     : https://prove2.me/theorems/ec21905d-7e53-4f37-9d7c-95f0450b3305
-- title:
--   UJClass Mass: stab T
-- statement:
--   The UJClass Mass construction uses the stab T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/SigRTmulOne.lean#L15-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/SigRTmulOne.lean#L15-L34

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PsiInclR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_SigRTmulOne
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
variable {M : ℕ}

theorem PI.UnitaryGroupMassFormula.UJClassMass.stabT (L : Set (Fin M → E)) {u k : ℕ} (hu : ∀ x ∈ L, ∀ i, IsIntegral ℤ ((u : F) • x i))
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L) {a : Af F} (ha : a ∈ intAf F)
    (Y : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (hY : ∀ i j, ∃ o ∈ Oh F E, (a ⊗ₜ[F] (1 : E)) * (Y - 1) i j = (u * k) • o)
    {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E L) :
    (a ⊗ₜ[F] (1 : E)) • Y.mulVec y ∈ latHat F E L := by sorry

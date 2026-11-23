-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_sfin_of_Lam_eq
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.sfin_of_Lam_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:59.071609+00:00
-- url     : https://prove2.me/theorems/78b50888-b5fb-4aec-9307-7a6bde79231e
-- title:
--   UJClass Fin: sfin of Lam eq
-- statement:
--   The UJClass Fin construction uses the sfin of Lam eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/Development.lean#L99-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/Development.lean#L99-L107

import Definitions.Def_Formalism_PeriodIntegrals_UJClassFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem PI.UnitaryGroupMassFormula.UJClassFin.sfin_of_Lam_eq (L : Set (Fin M → E))
    (hR : ∀ (h : HA (AF F) σ J) (y : Fin M → Af F ⊗[F] E),
      (finMat σ J h⁻¹).mulVec y ∈ latHat F E L ↔ y ∈ latHat F E (abelian₂ σ J L h))
    (h h' : HA (AF F) σ J) (he : abelian₂ σ J L h = abelian₂ σ J L h') : h⁻¹ * h' ∈ SFin σ J L := by sorry

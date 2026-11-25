-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_lvB_lat_down
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.lvB_lat_down
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:50:43.573989+00:00
-- url     : https://prove2.me/theorems/6ca5e8f4-2d6f-5008-8422-45aa0f3472c0
-- title:
--   In HHClass Fin: lv B lat down
-- statement:
--   The In HHClass Fin construction uses the lv B lat down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/LevelB.lean#L82-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/LevelB.lean#L82-L109

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Lemmata_IntegerMulIntegral_IntMulIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain Formalism.UG Formalism.UG.P PI.InHHClassFin
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem PI.UnitaryGroupMassFormula.InHHClassFin.lvB_lat_down (L : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ y : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      (∀ i, y i ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) →
      levelafC E d • y ∈ Formalism.MainNotions.S.lamAf (F := F) L := by sorry

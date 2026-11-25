-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_lvB_incl_int
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.lvB_incl_int
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:41:57.702675+00:00
-- url     : https://prove2.me/theorems/825e7ae8-666c-4ee3-a0aa-9bfd51985785
-- title:
--   In HHClass Fin: lv B incl int
-- statement:
--   The In HHClass Fin construction uses the lv B incl int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/LevelB.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/LevelB.lean#L26-L29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Lemmata_IntegerMulIntegral_IntMulIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelB
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.lvB_incl_int (a : 𝓞 E) : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) ∈
    tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by sorry

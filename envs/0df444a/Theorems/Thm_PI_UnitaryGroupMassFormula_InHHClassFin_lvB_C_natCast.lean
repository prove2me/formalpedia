-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_lvB_C_natCast
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.lvB_C_natCast
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:30:24.257743+00:00
-- url     : https://prove2.me/theorems/8f803f9b-2b91-5ad1-bde5-312ac0b5006b
-- title:
--   In HHClass Fin: lv B C nat Cast
-- statement:
--   The In HHClass Fin construction uses the lv B C nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/LevelB.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/LevelB.lean#L34-L35

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.lvB_C_natCast (M : ℕ) : levelafC E ((M : 𝓞 F)) = ((M : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by sorry

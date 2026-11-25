-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictInter_of_algebraMap_mem_intAd
-- name    : PIW.AdelClassFin.DictInter.of_algebraMap_mem_intAd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:49:37.130193+00:00
-- url     : https://prove2.me/theorems/b2a5f442-acff-442f-907c-550dccf405fa
-- title:
--   Dict Inter: of algebra Map mem int Ad
-- statement:
--   The Dict Inter construction uses the of algebra Map mem int Ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictInter.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictInter.lean#L63-L70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
open PIW.AdelClassFin.DictInter
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PIW.AdelClassFin.DictInter.of_algebraMap_mem_intAd (f : F) (h : algebraMap F (Af F) f ∈ Formalism.UG.intAd F) :
    f ∈ (algebraMap (𝓞 F) F).range := by sorry

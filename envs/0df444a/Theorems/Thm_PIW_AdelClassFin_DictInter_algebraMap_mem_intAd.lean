-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictInter_algebraMap_mem_intAd
-- name    : PIW.AdelClassFin.DictInter.algebraMap_mem_intAd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:48:11.824531+00:00
-- url     : https://prove2.me/theorems/44a2a095-9b60-4f82-a4fb-79396920e393
-- title:
--   Dict Inter: algebra Map mem int Ad
-- statement:
--   The Dict Inter construction uses the algebra Map mem int Ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictInter.lean#L47-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictInter.lean#L47-L61

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

theorem PIW.AdelClassFin.DictInter.algebraMap_mem_intAd (x : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F x) ∈ Formalism.UG.intAd F := by sorry

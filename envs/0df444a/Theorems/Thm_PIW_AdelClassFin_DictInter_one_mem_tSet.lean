-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictInter_one_mem_tSet
-- name    : PIW.AdelClassFin.DictInter.one_mem_tSet
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:58:35.435382+00:00
-- url     : https://prove2.me/theorems/cae510a8-33c5-525e-af78-374730961e83
-- title:
--   Dict Inter: one mem t Set
-- statement:
--   The Dict Inter construction uses the one mem t Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictInter.lean#L76-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictInter.lean#L76-L86

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

theorem PIW.AdelClassFin.DictInter.one_mem_tSet : (1 : E ⊗[F] Af F) ∈ tSet F E := by sorry

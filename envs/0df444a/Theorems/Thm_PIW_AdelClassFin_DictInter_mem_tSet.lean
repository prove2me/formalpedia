-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictInter_mem_tSet
-- name    : PIW.AdelClassFin.DictInter.mem_tSet
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:47:59.185182+00:00
-- url     : https://prove2.me/theorems/5deaaa4c-a0ee-445d-b2a6-0f80013f79fe
-- title:
--   Dict Inter: mem t Set
-- statement:
--   The Dict Inter construction uses the mem t Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictInter.lean#L96-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictInter.lean#L96-L142

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

theorem PIW.AdelClassFin.DictInter.mem_tSet (r : E ⊗[F] Af F) (hr : r ∈ IntAf F E) : r ∈ tSet F E := by sorry

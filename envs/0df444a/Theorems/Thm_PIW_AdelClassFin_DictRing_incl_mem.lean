-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictRing_incl_mem
-- name    : PIW.AdelClassFin.DictRing.incl_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:50:58.193739+00:00
-- url     : https://prove2.me/theorems/6b60c579-b5a7-5521-876f-55a118e82033
-- title:
--   Dict Ring: incl mem
-- statement:
--   The Dict Ring construction uses the incl mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictRing.lean#L181-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictRing.lean#L181-L182

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_DedekindLFunctions
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
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
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictRing
variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem PIW.AdelClassFin.DictRing.incl_mem (a : 𝓞 E) : Formalism.UG.inclE (F := F) (Af F) (a : E) ∈ IntAf F E := by sorry

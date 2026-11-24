-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictRing_incl_add
-- name    : PIW.AdelClassFin.DictRing.incl_add
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:22.179461+00:00
-- url     : https://prove2.me/theorems/f057a831-31a0-40b8-8796-722b5d97fd7f
-- title:
--   Dict Ring: incl add
-- statement:
--   The Dict Ring construction uses the incl add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictRing.lean#L184-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictRing.lean#L184-L185

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

theorem PIW.AdelClassFin.DictRing.incl_add (a b : 𝓞 E) : Formalism.UG.inclE (F := F) (Af F) ((a + b : 𝓞 E) : E) =
    Formalism.UG.inclE (F := F) (Af F) (a : E) + Formalism.UG.inclE (F := F) (Af F) (b : E) := by sorry

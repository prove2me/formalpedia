-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictRing_incl_neg
-- name    : PIW.AdelClassFin.DictRing.incl_neg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:32.148958+00:00
-- url     : https://prove2.me/theorems/4451a93e-b67f-42f3-8c2c-f48d738e2d44
-- title:
--   Dict Ring: incl neg
-- statement:
--   The Dict Ring construction uses the incl neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictRing.lean#L190-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictRing.lean#L190-L191

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

theorem PIW.AdelClassFin.DictRing.incl_neg (a : 𝓞 E) : Formalism.UG.inclE (F := F) (Af F) ((-a : 𝓞 E) : E) =
    -Formalism.UG.inclE (F := F) (Af F) (a : E) := by sorry

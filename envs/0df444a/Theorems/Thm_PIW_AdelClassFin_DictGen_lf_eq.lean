-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictGen_lf_eq
-- name    : PIW.AdelClassFin.DictGen.lf_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:29:36.449806+00:00
-- url     : https://prove2.me/theorems/a9e09347-da9b-48ed-8ed3-05a77d094929
-- title:
--   Dict Gen: lf eq
-- statement:
--   The Dict Gen construction uses the lf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L13-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
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
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictGen
variable (I : AutInst)

theorem PIW.AdelClassFin.DictGen.lf_eq : I.Lf = Submodule.span (IntAf I.F I.E)
    (Set.range fun x : I.L => iv I (x : Fin I.n → I.E)) := by sorry

-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictGen_iv_nsmul
-- name    : PIW.AdelClassFin.DictGen.iv_nsmul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:40.165851+00:00
-- url     : https://prove2.me/theorems/7e23010d-a0d1-4413-9244-d5bcf132a907
-- title:
--   Dict Gen: iv nsmul
-- statement:
--   The Dict Gen construction uses the iv nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L29-L34

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

theorem PIW.AdelClassFin.DictGen.iv_nsmul (N : ℕ) (v : Fin I.n → I.E) :
    iv I (N • v) = (N : I.E ⊗[I.F] Af I.F) • iv I v := by sorry

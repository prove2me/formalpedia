-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictLat_iv_single
-- name    : PIW.AdelClassFin.DictLat.iv_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:49:07.028233+00:00
-- url     : https://prove2.me/theorems/62b5e2a7-cb80-45da-87a8-10475b5f8688
-- title:
--   Dict Lat: iv single
-- statement:
--   The Dict Lat construction uses the iv single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictLat.lean#L190-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictLat.lean#L190-L194

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictLat
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

theorem PIW.AdelClassFin.DictLat.iv_single (I : AutInst) (i : Fin I.n) :
    iv I (Pi.single i (1 : I.E)) = Pi.single i (1 : I.E ⊗[I.F] Af I.F) := by sorry

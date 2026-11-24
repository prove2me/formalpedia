-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictLat_hhat_iv
-- name    : PIW.AdelClassFin.DictLat.hhat_iv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:44:17.764399+00:00
-- url     : https://prove2.me/theorems/c063642f-515a-4d53-ae4d-0eeb8932e250
-- title:
--   Dict Lat: hhat iv
-- statement:
--   The Dict Lat construction uses the hhat iv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictLat.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictLat.lean#L47-L49

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

theorem PIW.AdelClassFin.DictLat.hhat_iv (I : AutInst) (v w : Fin I.n → I.E) :
    hhat I (iv I v) (iv I w) = Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J v w) := by sorry

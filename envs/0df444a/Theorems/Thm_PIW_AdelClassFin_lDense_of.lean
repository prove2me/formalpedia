-- Prove2me | Theorems.Thm_PIW_AdelClassFin_lDense_of
-- name    : PIW.AdelClassFin.lDense_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:30:09.724681+00:00
-- url     : https://prove2.me/theorems/d31bffc2-b8b5-4228-bc07-05d6a7fe0ba9
-- title:
--   Adel Class Fin: l Dense of
-- statement:
--   The Adel Class Fin construction uses the l Dense of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictLat.lean#L238-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictLat.lean#L238-L243

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

theorem PIW.AdelClassFin.lDense_of (h : DDense) : LDense := by sorry

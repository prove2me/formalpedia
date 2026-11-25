-- Prove2me | Theorems.Thm_PIW_AdelClassFin_mGen_of
-- name    : PIW.AdelClassFin.mGen_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:48:16.014806+00:00
-- url     : https://prove2.me/theorems/64b0cb88-420e-45a8-b240-90b5527d4a3a
-- title:
--   Adel Class Fin: m Gen of
-- statement:
--   The Adel Class Fin construction uses the m Gen of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L188-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L188-L231

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

theorem PIW.AdelClassFin.mGen_of (hD : LDenom) (hDen : LDense) : MGen := by sorry

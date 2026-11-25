-- Prove2me | Theorems.Thm_PIW_AdelClassFin_stLatFin_of
-- name    : PIW.AdelClassFin.stLatFin_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:29:28.458272+00:00
-- url     : https://prove2.me/theorems/8cf7d1c0-a4a9-469f-baf8-7dc37cb5b4c9
-- title:
--   Adel Class Fin: st Lat Fin of
-- statement:
--   The Adel Class Fin construction uses the st Lat Fin of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/KsetMulVecMem.lean#L120-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/KsetMulVecMem.lean#L120-L133

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_KsetMulVecMem
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

theorem PIW.AdelClassFin.stLatFin_of (h : LDense) : StLatFin := by sorry

-- Prove2me | Theorems.Thm_PIW_AdelClassFin_stDict_of
-- name    : PIW.AdelClassFin.stDict_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:48:47.34439+00:00
-- url     : https://prove2.me/theorems/05c8c72c-ef32-4386-825e-b0b96ce96b3c
-- title:
--   Adel Class Fin: st Dict of
-- statement:
--   The Adel Class Fin construction uses the st Dict of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictPlan.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictPlan.lean#L86-L87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelClassFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
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

theorem PIW.AdelClassFin.stDict_of (h1 : MLat) (h2 : MDual) (h3 : MInj) (h4 : MEquiv) : StDict := by sorry

-- Prove2me | Theorems.Thm_PI_FinKW_memLocFrom_of
-- name    : PI.FinKW.memLocFrom_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:31:02.90781+00:00
-- url     : https://prove2.me/theorems/6fe08595-635d-4b5d-afaf-9e4d2ca1c27c
-- title:
--   Fin KW: mem Loc From of
-- statement:
--   The Fin KW construction uses the mem Loc From of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocFrom.lean#L42-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocFrom.lean#L42-L95

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinKW
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

theorem PI.FinKW.memLocFrom_of (hI : InjV) : MemLocFrom := by sorry

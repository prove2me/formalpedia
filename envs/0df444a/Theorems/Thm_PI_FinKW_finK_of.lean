-- Prove2me | Theorems.Thm_PI_FinKW_finK_of
-- name    : PI.FinKW.finK_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:44.399654+00:00
-- url     : https://prove2.me/theorems/6374a6b7-b8fc-4564-a71d-6b4190562d88
-- title:
--   Fin KW: fin K of
-- statement:
--   The Fin KW construction uses the fin K of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/VecVMulVec.lean#L42-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/VecVMulVec.lean#L42-L83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_VecVMulVec
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
open Formalism.L2.SG.AdBridge

theorem PI.FinKW.finK_of (hT : MemLocTo) (hF : MemLocFrom) (hS : LiftV) : PI.AdBridgeSteps.FinK := by sorry

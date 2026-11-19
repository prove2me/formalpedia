-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_mem_l2_dual_iff_exists_l1_plus_allOnes
-- name    : QEC.Distillation.BK15.mem_l2_dual_iff_exists_l1_plus_allOnes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:02:23.653861+00:00
-- url     : https://prove2.me/theorems/148041f2-6337-4aef-941a-9a4606141f85
-- title:
--   BK15: mem l2 dual iff exists l1 plus all Ones
-- statement:
--   A dual `L2` word has a unique concrete `L1 + c[1]` decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L360-L371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L360-L371

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.mem_l2_dual_iff_exists_l1_plus_allOnes (w : Word) :
    w ∈ L2.dual.carrier ↔
      ∃ a : Fin 4 → Bit, ∃ c : Bit,
        w = l1CoefficientMap a + c • allOnes := by sorry

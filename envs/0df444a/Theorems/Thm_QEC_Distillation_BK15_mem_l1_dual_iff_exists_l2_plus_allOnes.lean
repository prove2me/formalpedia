-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_mem_l1_dual_iff_exists_l2_plus_allOnes
-- name    : QEC.Distillation.BK15.mem_l1_dual_iff_exists_l2_plus_allOnes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:03:14.214133+00:00
-- url     : https://prove2.me/theorems/75a6af21-2466-4dff-bf70-8c3e77625041
-- title:
--   BK15: mem l1 dual iff exists l2 plus all Ones
-- statement:
--   A dual `L1` word has a unique concrete `L2 + c[1]` decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L346-L357
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L346-L357

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.mem_l1_dual_iff_exists_l2_plus_allOnes (w : Word) :
    w ∈ L1.dual.carrier ↔
      ∃ b : Sum (Fin 4) QuadraticIndex → Bit, ∃ c : Bit,
        w = l2CoefficientMap b + c • allOnes := by sorry

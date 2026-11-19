-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l2_dual_decomposition_unique
-- name    : QEC.Distillation.BK15.l2_dual_decomposition_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:02:33.454652+00:00
-- url     : https://prove2.me/theorems/312974fa-26df-4424-8c58-d45c37f5213d
-- title:
--   BK15: l2 dual decomposition unique
-- statement:
--   The `L1 + c[1]` decomposition is unique.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L383-L389
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L383-L389

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l2_dual_decomposition_unique
    {a a' : Fin 4 → Bit} {c c' : Bit}
    (h : l1CoefficientMap a + c • allOnes = l1CoefficientMap a' + c' • allOnes) :
    a = a' ∧ c = c' := by sorry

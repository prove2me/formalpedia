-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_l1_dual_decomposition_unique
-- name    : QEC.Distillation.BK15.l1_dual_decomposition_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:02:26.509031+00:00
-- url     : https://prove2.me/theorems/3e8649b1-05bd-468e-8cab-d5e268d51c18
-- title:
--   BK15: l1 dual decomposition unique
-- statement:
--   The `L2 + c[1]` decomposition is unique.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L374-L380
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean#L374-L380

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding

theorem QEC.Distillation.BK15.l1_dual_decomposition_unique
    {b b' : Sum (Fin 4) QuadraticIndex → Bit} {c c' : Bit}
    (h : l2CoefficientMap b + c • allOnes = l2CoefficientMap b' + c' • allOnes) :
    b = b' ∧ c = c' := by sorry

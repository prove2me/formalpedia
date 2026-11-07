-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_6_8
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_6_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:56:20.807139+00:00
-- url     : https://prove2.me/theorems/6d7831a8-3c3a-4331-aa33-54f364b677c2
-- title:
--   Why24 Appendix ANF: source Coefficient triple 6 8
-- statement:
--   Cubic coefficient certificate with fixed first indices 6, 8.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part15.lean#L151-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part15.lean#L151-L173

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part15
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_6_8 (third : Fin 10)
    (hlt : (8 : Fin 10) < third) :
    sourceTripleCoefficient 6 8 third = cubicGateCoefficient 6 8 third := by sorry

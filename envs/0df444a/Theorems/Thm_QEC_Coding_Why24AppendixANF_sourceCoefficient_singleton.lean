-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_singleton
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:35:13.591819+00:00
-- url     : https://prove2.me/theorems/3d8d9eef-e00a-4f34-b58c-6fc10b4197d0
-- title:
--   Why24 Appendix ANF: source Coefficient singleton
-- statement:
--   The ten linear WHY24 coefficients.  Each independent certificate reduces
--   one sparse coefficient of the compositional cubic construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Certificate.lean#L143-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Certificate.lean#L143-L155

import Definitions.Def_QEC_Coding_QuditQubitConversion_BooleanANF
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Certificate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_singleton (coordinate : Fin 10) :
    sourceCoefficient {coordinate} = 1 := by sorry

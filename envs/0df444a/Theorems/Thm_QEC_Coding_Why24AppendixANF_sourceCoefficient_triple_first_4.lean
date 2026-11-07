-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_first_4
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_first_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:06:49.804097+00:00
-- url     : https://prove2.me/theorems/11a888a8-610c-413b-9089-43f3797d0de1
-- title:
--   Why24 Appendix ANF: source Coefficient triple first 4
-- statement:
--   Cubic coefficient certificate with fixed first index 4.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Certificate.lean#L109-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Certificate.lean#L109-L128

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part00
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part01
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part02
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part03
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part04
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part05
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part06
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part07
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part08
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part09
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part10
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part11
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part12
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part13
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part14
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part15
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Certificate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_first_4 (second third : Fin 10)
    (hfirst : (4 : Fin 10) < second) (hsecond : second < third) :
    sourceTripleCoefficient 4 second third = cubicGateCoefficient 4 second third := by sorry

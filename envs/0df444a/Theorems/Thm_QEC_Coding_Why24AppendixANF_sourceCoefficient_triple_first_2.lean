-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_first_2
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_first_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:05:58.078101+00:00
-- url     : https://prove2.me/theorems/0f6857bc-8e0a-44fc-99ec-be2b7ee7cae5
-- title:
--   Why24 Appendix ANF: source Coefficient triple first 2
-- statement:
--   Cubic coefficient certificate with fixed first index 2.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Certificate.lean#L68-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Certificate.lean#L68-L85

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

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_first_2 (second third : Fin 10)
    (hfirst : (2 : Fin 10) < second) (hsecond : second < third) :
    sourceTripleCoefficient 2 second third = cubicGateCoefficient 2 second third := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_why24AppendixRetainedSites_eq_source
-- name    : QEC.Coding.why24AppendixRetainedSites_eq_source
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:42:07.87463+00:00
-- url     : https://prove2.me/theorems/52ea0b17-5819-4f60-9b97-08511c71ef6f
-- title:
--   Coding: why24 Appendix Retained Sites eq source
-- statement:
--   The retained source sites are exactly `0,1,2`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ReversePhase.lean#L25-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ReversePhase.lean#L25-L27

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding

theorem QEC.Coding.why24AppendixRetainedSites_eq_source :
    why24AppendixRetainedSites = ({0, 1, 2} : Finset (Fin 10)) := by sorry

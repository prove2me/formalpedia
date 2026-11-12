-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18BinomialTailAsymptotics_binomialTail_le_two_pow
-- name    : QEC.Distillation.HH18.HH18BinomialTailAsymptotics.binomialTail_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:00:58.156202+00:00
-- url     : https://prove2.me/theorems/c0e94ee2-fb41-4a46-b328-7392a9ca7929
-- title:
--   HH18 Binomial Tail Asymptotics: binomial Tail le two pow
-- statement:
--   Every binomial tail is bounded by the full binomial row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/BinomialTailAsymptotics.lean#L23-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/BinomialTailAsymptotics.lean#L23-L33

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Mathlib.Analysis.SpecialFunctions.Stirling
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18BinomialTailAsymptotics
open Coding.PuncturedReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18BinomialTailAsymptotics.binomialTail_le_two_pow (n w : Nat) : binomialTail n w ≤ 2 ^ n := by sorry

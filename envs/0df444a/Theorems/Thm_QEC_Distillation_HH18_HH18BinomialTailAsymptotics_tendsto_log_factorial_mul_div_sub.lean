-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18BinomialTailAsymptotics_tendsto_log_factorial_mul_div_sub
-- name    : QEC.Distillation.HH18.HH18BinomialTailAsymptotics.tendsto_log_factorial_mul_div_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:33:56.702468+00:00
-- url     : https://prove2.me/theorems/05914983-a057-41c7-8b6b-6dcfebcceb88
-- title:
--   HH18 Binomial Tail Asymptotics: tendsto log factorial mul div sub
-- statement:
--   Stirling's normalized log-factorial limit along a positive integral ray.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/BinomialTailAsymptotics.lean#L80-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/BinomialTailAsymptotics.lean#L80-L109

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Mathlib.Analysis.SpecialFunctions.Stirling
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18BinomialTailAsymptotics
open Coding.PuncturedReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18BinomialTailAsymptotics.tendsto_log_factorial_mul_div_sub (a : Nat) (ha : 0 < a) : Tendsto
    (fun j : Nat => Real.log ((a * j).factorial : ℝ) / j - a * Real.log j)
    atTop (𝓝 (a * Real.log a - a)) := by sorry

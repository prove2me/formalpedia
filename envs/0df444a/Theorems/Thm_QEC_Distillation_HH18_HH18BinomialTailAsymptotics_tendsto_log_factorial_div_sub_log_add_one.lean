-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18BinomialTailAsymptotics_tendsto_log_factorial_div_sub_log_add_one
-- name    : QEC.Distillation.HH18.HH18BinomialTailAsymptotics.tendsto_log_factorial_div_sub_log_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:00:52.544516+00:00
-- url     : https://prove2.me/theorems/86e33121-f19a-4701-b4de-86f9ef0aecc3
-- title:
--   HH18 Binomial Tail Asymptotics: tendsto log factorial div sub log add one
-- statement:
--   The logarithm of `n!`, normalized by `n`, has its Stirling leading term.
--
--   This is the factorial component needed to turn the finite HH18 binomial sums
--   into proportional entropy exponents.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/BinomialTailAsymptotics.lean#L39-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/BinomialTailAsymptotics.lean#L39-L77

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Mathlib.Analysis.SpecialFunctions.Stirling
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18BinomialTailAsymptotics
open Coding.PuncturedReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18BinomialTailAsymptotics.tendsto_log_factorial_div_sub_log_add_one : Tendsto
    (fun n : Nat => Real.log (n.factorial : ℝ) / n - Real.log n + 1)
    atTop (𝓝 0) := by sorry

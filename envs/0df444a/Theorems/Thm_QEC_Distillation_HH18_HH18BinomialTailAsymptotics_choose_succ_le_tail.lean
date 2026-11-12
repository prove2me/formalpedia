-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18BinomialTailAsymptotics_choose_succ_le_tail
-- name    : QEC.Distillation.HH18.HH18BinomialTailAsymptotics.choose_succ_le_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:42:54.005493+00:00
-- url     : https://prove2.me/theorems/14827b04-10a1-48f2-abe2-719c9038c67a
-- title:
--   HH18 Binomial Tail Asymptotics: choose succ le tail
-- statement:
--   The first summand of a nonempty binomial tail lower-bounds the tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/BinomialTailAsymptotics.lean#L17-L20
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/BinomialTailAsymptotics.lean#L17-L20

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Mathlib.Analysis.SpecialFunctions.Stirling
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18BinomialTailAsymptotics
open Coding.PuncturedReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18BinomialTailAsymptotics.choose_succ_le_tail (n w : Nat) (h : w + 1 ≤ n) :
    Nat.choose n (w + 1) ≤ binomialTail n w := by sorry

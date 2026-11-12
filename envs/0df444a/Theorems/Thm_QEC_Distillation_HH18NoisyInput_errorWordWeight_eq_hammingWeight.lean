-- Prove2me | Theorems.Thm_QEC_Distillation_HH18NoisyInput_errorWordWeight_eq_hammingWeight
-- name    : QEC.Distillation.HH18NoisyInput.errorWordWeight_eq_hammingWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:40:45.951119+00:00
-- url     : https://prove2.me/theorems/e7677b33-e34c-49b1-bfeb-adcd0c8af4d2
-- title:
--   HH18 Noisy Input: error Word Weight eq hamming Weight
-- statement:
--   The literal product law separates the error support from its complement.
--   This is an identity for the actual diagonal resource distribution, not an
--   enumerator supplied to a later protocol layer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean#L209-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean#L209-L256

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18NoisyInput
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
universe u

theorem QEC.Distillation.HH18NoisyInput.errorWordWeight_eq_hammingWeight {ι : Type u} [Fintype ι] [DecidableEq ι]
    (epsilon : DiagonalErrorRate) (error : Word (ZMod 2) ι) :
    errorWordWeight epsilon error =
      epsilon.1 ^ HammingWeight error *
        (1 - epsilon.1) ^ (Fintype.card ι - HammingWeight error) := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19FixedPrimeActualOutputError_le_scheduleTargetError
-- name    : QEC.Distillation.KT19VanishingOverhead.kt19FixedPrimeActualOutputError_le_scheduleTargetError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:43:20.533754+00:00
-- url     : https://prove2.me/theorems/29171443-bfdb-4e42-8a5a-480ef13ca80f
-- title:
--   KT19 Vanishing Overhead: kt19 Fixed Prime Actual Output Error le schedule Target Error
-- statement:
--   The public actual output error is bounded by the explicit fixed-prime
--   target schedule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/VanishingOverhead.lean#L2986-L2998
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/VanishingOverhead.lean#L2986-L2998

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_VanishingOverhead
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19VanishingOverhead
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19Protocol
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open Filter Topology
open scoped BigOperators
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.KT19VanishingOverhead.instKT19VanishingOverheadClassicalDecidable
attribute [local instance] QEC.Distillation.KT19VanishingOverhead.instKT19VanishingOverheadClassicalDecidable
universe u
variable {p l k : Nat} [NeZero p] [Fact p.Prime]

theorem QEC.Distillation.KT19VanishingOverhead.kt19FixedPrimeActualOutputError_le_scheduleTargetError
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4)
    (depth : Nat) :
    kt19FixedPrimeActualOutputError family mu hmu_nonneg hmu_sum depth ≤
      kt19FixedPrimeScheduleTargetError family mu depth := by sorry

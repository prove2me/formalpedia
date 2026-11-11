-- Prove2me | Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19FixedPrime
-- name    : QEC.Distillation.KT19VanishingOverhead.kt19FixedPrime
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T11:28:07.968566+00:00
-- url     : https://prove2.me/theorems/560dd55b-3602-450e-8298-54bd228200e7
-- title:
--   KT19 Vanishing Overhead: kt19 Fixed Prime
-- statement:
--   The complete fixed-prime KT19 construction: literal selected-path runs
--   have vanishing physical output error and a typed successful-output cost bound
--   at the required logarithmic exponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/VanishingOverhead.lean#L3257-L3287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/VanishingOverhead.lean#L3257-L3287

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

theorem QEC.Distillation.KT19VanishingOverhead.kt19FixedPrime
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (hdistance : 2 ≤ l - k)
    (hepsilon : 0 < kt19ErrorRate mu)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4) :
    Tendsto (fun depth : Nat =>
      kt19FixedPrimeScheduleTargetError family mu depth) atTop (𝓝 0) ∧
      Tendsto (fun depth : Nat =>
        kt19FixedPrimeActualOutputError family mu hmu_nonneg hmu_sum depth)
        atTop (𝓝 0) ∧
      DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
        (fun depth => kt19FixedPrimeInputSlots p k depth)
        (fun depth => kt19FixedPrimeOutputSlots k depth)
        (kt19FixedPrimeScheduleTargetError family mu)
        (kt19FixedPrimeActualOutputError family mu hmu_nonneg hmu_sum)
        (kt19FixedPrimeExpectedYield family mu hmu_nonneg hmu_sum)
        (kt19FixedPrimeGamma p l k) (kt19FixedPrimeCostCoefficient family mu) := by sorry

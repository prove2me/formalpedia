-- Prove2me | Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19FixedPrimeSuccessfulOutputCost_le_six_fifths
-- name    : QEC.Distillation.KT19VanishingOverhead.kt19FixedPrimeSuccessfulOutputCost_le_six_fifths
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:17:45.30621+00:00
-- url     : https://prove2.me/theorems/59197b0b-00dd-41d0-9706-c91dd48762f3
-- title:
--   KT19 Vanishing Overhead: kt19 Fixed Prime Successful Output Cost le six fifths
-- statement:
--   The literal typed successful-output cost is controlled by the same
--   uniform physical pooled-yield lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/VanishingOverhead.lean#L3052-L3079
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/VanishingOverhead.lean#L3052-L3079

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

theorem QEC.Distillation.KT19VanishingOverhead.kt19FixedPrimeSuccessfulOutputCost_le_six_fifths
    (family : KT19DistillationFamily p l k) (mu : ZMod p → ℝ)
    (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (hdistance : 2 ≤ l - k)
    (hsmall : kt19FixedPrimeIterationScale family * kt19ErrorRate mu ≤ 1 / 4)
    (depth : Nat) :
    kt19FixedPrimeSuccessfulOutputCost family mu hmu_nonneg hmu_sum depth ≤
      (6 / 5 : ℝ) * ((((p - k : Nat) : ℝ) / (k : ℝ)) ^ depth) := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19SelectedPortErrorRate_eq_outputPortError
-- name    : QEC.Distillation.KT19VanishingOverhead.kt19SelectedPortErrorRate_eq_outputPortError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:36:36.704229+00:00
-- url     : https://prove2.me/theorems/6f519c28-69ca-4b6d-a36f-93b61e73e311
-- title:
--   KT19 Vanishing Overhead: kt19 Selected Port Error Rate eq output Port Error
-- statement:
--   The nonzero-label rate of the actual one-port marginal is exactly the
--   corresponding physical decoded-output port error.  This is a finite
--   partition-of-labels identity, independent of the later density-factorization
--   bridge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/VanishingOverhead.lean#L1342-L1379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/VanishingOverhead.lean#L1342-L1379

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

theorem QEC.Distillation.KT19VanishingOverhead.kt19SelectedPortErrorRate_eq_outputPortError
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k) :
    kt19ErrorRate (kt19SelectedPortLabelDistribution
      family mu hmu_nonneg hmu_sum port) =
      kt19OutputPortError (family.run mu hmu_nonneg hmu_sum).acceptedOutput port := by sorry

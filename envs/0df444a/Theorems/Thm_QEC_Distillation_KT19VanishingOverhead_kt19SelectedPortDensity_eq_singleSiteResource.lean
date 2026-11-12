-- Prove2me | Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19SelectedPortDensity_eq_singleSiteResource
-- name    : QEC.Distillation.KT19VanishingOverhead.kt19SelectedPortDensity_eq_singleSiteResource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:02:08.256748+00:00
-- url     : https://prove2.me/theorems/52098f18-ad80-4321-a8a8-ce06d93d37a4
-- title:
--   KT19 Vanishing Overhead: kt19 Selected Port Density eq single Site Resource
-- statement:
--   The actual singleton marginal of the normalized accepted KT19 output is
--   exactly the one-site KT19 resource at its physically induced selected-label
--   distribution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/VanishingOverhead.lean#L1637-L1664
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/VanishingOverhead.lean#L1637-L1664

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

theorem QEC.Distillation.KT19VanishingOverhead.kt19SelectedPortDensity_eq_singleSiteResource
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) (port : Fin k)
    (heps : kt19ErrorRate mu < 1) :
    kt19SelectedPortDensity family mu hmu_nonneg hmu_sum port =
      kt19SingleSiteResource
        (kt19SelectedPortLabelDistribution family mu hmu_nonneg hmu_sum port)
        (kt19SelectedPortLabelDistribution_nonneg family mu hmu_nonneg hmu_sum port)
        (kt19SelectedPortLabelDistribution_sum family mu hmu_nonneg hmu_sum port) := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_KT19VanishingOverhead_kt19ChangingPrimeExponent
-- name    : QEC.Distillation.KT19VanishingOverhead.kt19ChangingPrimeExponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:28:16.710011+00:00
-- url     : https://prove2.me/theorems/ddc23c92-349d-4185-b0f6-3052a75a8933
-- title:
--   KT19 Vanishing Overhead: kt19 Changing Prime Exponent
-- statement:
--   For every lower prime cutoff and positive tolerance, an actual larger
--   prime KT19 parameter choice has a strictly smaller displayed exponent.  The
--   prime is selected on the literal `1 (mod 8)` ray, so the accompanying
--   `kt19ExplicitDistillationFamily` is constructed from its Lagrange/nodal rows
--   by the existing definition rather than supplied as an asymptotic shell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/VanishingOverhead.lean#L3331-L3369
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/VanishingOverhead.lean#L3331-L3369

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

theorem QEC.Distillation.KT19VanishingOverhead.kt19ChangingPrimeExponent (bound : Nat) (eta : ℝ) (heta : 0 < eta) :
    ∃ p : Nat, bound ≤ p ∧ Nat.Prime p ∧ 32 ≤ p ∧ p ≡ 1 [MOD 8] ∧
      kt19FixedPrimeGamma p (kt19ExplicitL p) (kt19ExplicitK p) < eta := by sorry

-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_singleOddExtensionCode_dual_bernoulliMass_eq_weightSum
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.singleOddExtensionCode_dual_bernoulliMass_eq_weightSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:08:01.653713+00:00
-- url     : https://prove2.me/theorems/a702a2f5-2a35-4985-be2e-97144d8e6f82
-- title:
--   BH12 Protocol: single Odd Extension Code dual bernoulli Mass eq weight Sum
-- statement:
--   The finite extension-code character calculation evaluates the literal
--   zero-marginal dual Bernoulli mass from the actual 16-word enumerator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2397-L2406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2397-L2406

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.Triorthogonal.BH12Protocol.singleOddExtensionCode_dual_bernoulliMass_eq_weightSum (q : Nat)
    (a : OddRow q) (p : ErrorParameter) :
    (∑ error : (singleOddExtensionCode a).dual.carrier,
      errorWordProbability p (error : PhysicalError q)) =
      (16 : ℝ)⁻¹ *
        codeWeightSum (singleOddExtensionCode a)
          (fun weight => (1 - 2 * p.rate) ^ weight) := by sorry

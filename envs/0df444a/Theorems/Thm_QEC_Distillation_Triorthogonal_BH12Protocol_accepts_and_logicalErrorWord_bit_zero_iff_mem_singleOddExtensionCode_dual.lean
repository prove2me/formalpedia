-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_accepts_and_logicalErrorWord_bit_zero_iff_mem_singleOddExtensionCode_dual
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.accepts_and_logicalErrorWord_bit_zero_iff_mem_singleOddExtensionCode_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:06:08.039725+00:00
-- url     : https://prove2.me/theorems/0a1d9428-4f9a-4b82-b50c-d7d553d23bbd
-- title:
--   BH12 Protocol: accepts and logical Error Word bit zero iff mem single Odd Extension Code dual
-- statement:
--   The source's zero marginal sector is the dual of the actual extension
--   `G₀ + ⟨gᵃ⟩`, not an assumed output formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2088-L2120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2088-L2120

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.accepts_and_logicalErrorWord_bit_zero_iff_mem_singleOddExtensionCode_dual
    (q : Nat) (a : OddRow q) (error : PhysicalError q) :
    Accepts error ∧ logicalErrorWord error a = 0 ↔
      error ∈ (singleOddExtensionCode a).dual.carrier := by sorry

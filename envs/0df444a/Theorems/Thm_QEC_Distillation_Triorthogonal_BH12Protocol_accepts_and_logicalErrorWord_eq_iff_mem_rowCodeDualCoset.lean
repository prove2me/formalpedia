-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_accepts_and_logicalErrorWord_eq_iff_mem_rowCodeDualCoset
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.accepts_and_logicalErrorWord_eq_iff_mem_rowCodeDualCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:06:42.515697+00:00
-- url     : https://prove2.me/theorems/7caf9e97-fe31-413a-b45a-911662439b64
-- title:
--   BH12 Protocol: accepts and logical Error Word eq iff mem row Code Dual Coset
-- statement:
--   An accepted error has logical label `x` exactly when it lies in the
--   physical affine coset `G⊥ + \sum_a x_a g^a`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1970-L2016
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1970-L2016

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.accepts_and_logicalErrorWord_eq_iff_mem_rowCodeDualCoset (q : Nat)
    (error : PhysicalError q) (logical : Word (ZMod 2) (OddRow q)) :
    Accepts error ∧ logicalErrorWord error = logical ↔
      error - (family q).oddCombination logical ∈
        (family q).rowCode.dual.carrier := by sorry

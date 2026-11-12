-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_rawLogicalErrorWeight_eq_rowCodeDualCosetBernoulliMass
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.rawLogicalErrorWeight_eq_rowCodeDualCosetBernoulliMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:46:26.369362+00:00
-- url     : https://prove2.me/theorems/735787cd-19d8-46ef-93aa-05ba5b46f307
-- title:
--   BH12 Protocol: raw Logical Error Weight eq row Code Dual Coset Bernoulli Mass
-- statement:
--   The accepted physical branches give the literal source `G⊥`-coset
--   distribution on decoded logical error words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2020-L2039
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2020-L2039

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.rawLogicalErrorWeight_eq_rowCodeDualCosetBernoulliMass (q : Nat)
    (p : ErrorParameter) (logical : Word (ZMod 2) (OddRow q)) :
    rawLogicalErrorWeight q p logical =
      rowCodeDualCosetBernoulliMass q p logical := by sorry

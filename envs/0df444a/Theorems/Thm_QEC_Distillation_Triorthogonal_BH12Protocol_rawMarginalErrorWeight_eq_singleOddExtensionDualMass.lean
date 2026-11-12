-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_rawMarginalErrorWeight_eq_singleOddExtensionDualMass
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.rawMarginalErrorWeight_eq_singleOddExtensionDualMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:07:07.521369+00:00
-- url     : https://prove2.me/theorems/f90bd769-9f97-4595-bb96-05ab22fbf918
-- title:
--   BH12 Protocol: raw Marginal Error Weight eq single Odd Extension Dual Mass
-- statement:
--   The raw marginal is the accepted mass minus the actual dual mass of the
--   zero-logical-bit extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2137-L2196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2137-L2196

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.rawMarginalErrorWeight_eq_singleOddExtensionDualMass (q : Nat)
    (p : ErrorParameter) (a : OddRow q) :
    rawMarginalErrorWeight q p a =
      rawSuccessMass q p -
        ∑ error : (singleOddExtensionCode a).dual.carrier,
          errorWordProbability p (error : PhysicalError q) := by sorry

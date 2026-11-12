-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisNegativeWeight_resourceDecodedRun_acceptedOutput
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisNegativeWeight_resourceDecodedRun_acceptedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:12:59.154775+00:00
-- url     : https://prove2.me/theorems/6d0b1513-f4bd-44f1-b8a6-beea57fca95e
-- title:
--   BH12 Protocol: logical ABasis Negative Weight resource Decoded Run accepted Output
-- statement:
--   The negative-A weight measured on the actual successful decoded run is
--   the normalized physical accepted mass whose derived logical bit is one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3181-L3221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3181-L3221

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisNegativeWeight_resourceDecodedRun_acceptedOutput
    (q : Nat) (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p)
    (a : OddRow q) :
    logicalABasisNegativeWeight a
        (resourceDecodedRun q (noisyResources q p)).acceptedOutput =
      decodedMarginalError q p hsuccess a := by sorry

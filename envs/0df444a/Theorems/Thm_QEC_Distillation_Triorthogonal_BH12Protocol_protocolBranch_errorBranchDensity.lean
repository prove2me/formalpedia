-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_protocolBranch_errorBranchDensity
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.protocolBranch_errorBranchDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:04:04.413643+00:00
-- url     : https://prove2.me/theorems/b746d9d1-d9ec-4839-b0e0-dbcda1d74ec6
-- title:
--   BH12 Protocol: protocol Branch error Branch Density
-- statement:
--   The coarse instrument selects exactly the deterministic syndrome endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L525-L547
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L525-L547

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.protocolBranch_errorBranchDensity (q : Nat) (error : PhysicalError q)
    (outcome : DistillationOutcome) :
    (protocolSyndromeInstrument q).branchOperator outcome
        (errorBranchDensity error).toOperator =
      if syndromeOutcome (syndromeOfError error) = outcome
        then (errorBranchDensity error).toOperator else 0 := by sorry

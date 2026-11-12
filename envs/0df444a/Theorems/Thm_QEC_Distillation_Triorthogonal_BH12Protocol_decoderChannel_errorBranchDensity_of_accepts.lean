-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_decoderChannel_errorBranchDensity_of_accepts
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.decoderChannel_errorBranchDensity_of_accepts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:10:03.094847+00:00
-- url     : https://prove2.me/theorems/32a723f1-54e4-493b-ba89-b7995d9f9b43
-- title:
--   BH12 Protocol: decoder Channel error Branch Density of accepts
-- statement:
--   The actual decoder maps every accepted physical pure branch to the pure
--   logical density labelled by its derived odd-row error word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3008-L3014
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3008-L3014

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.decoderChannel_errorBranchDensity_of_accepts {q : Nat}
    (error : PhysicalError q) (haccept : Accepts error) :
    decoderChannel q (errorBranchDensity error).toOperator =
      (logicalErrorDensity (logicalErrorWord error)).toOperator := by sorry

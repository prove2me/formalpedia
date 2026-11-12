-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decoderChannel_rankOne_physicalTInv_eq_idealLogicalTOutput
-- name    : QEC.Distillation.HH18Parameterized.decoderChannel_rankOne_physicalTInv_eq_idealLogicalTOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:00:52.799954+00:00
-- url     : https://prove2.me/theorems/daf7a65b-7828-4d1f-b412-8110669e77a3
-- title:
--   HH18 Parameterized: decoder Channel rank One physical TInv eq ideal Logical TOutput
-- statement:
--   Decoding the actual error-free inverse physical-`T` rank-one branch
--   returns the parameterized logical-`T` ideal density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Decoder.lean#L292-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Decoder.lean#L292-L302

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.HH18Parameterized.decoderChannel_rankOne_physicalTInv_eq_idealLogicalTOutput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    decoderChannel h (InnerProductSpace.rankOne Complex
      (physicalTInvBranch h hdegree) (physicalTInvBranch h hdegree)).toLinearMap =
      (idealLogicalTOutput m w).toOperator := by sorry

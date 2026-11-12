-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_decoderChannel_rankOne_encoded
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.decoderChannel_rankOne_encoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:04:22.023899+00:00
-- url     : https://prove2.me/theorems/3ff65804-a1f8-4f45-a70b-057c274067d8
-- title:
--   BH12 Protocol: decoder Channel rank One encoded
-- statement:
--   The BH12 Protocol construction uses the decoder Channel rank One encoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1328-L1356
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1328-L1356

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.decoderChannel_rankOne_encoded (q : Nat)
    (psi : LogicalRegister q) :
    decoderChannel q
        (InnerProductSpace.rankOne Complex
          (ambientEncodingIsometry q psi)
          (ambientEncodingIsometry q psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by sorry

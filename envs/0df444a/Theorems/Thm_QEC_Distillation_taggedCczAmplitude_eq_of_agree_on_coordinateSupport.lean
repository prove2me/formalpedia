-- Prove2me | Theorems.Thm_QEC_Distillation_taggedCczAmplitude_eq_of_agree_on_coordinateSupport
-- name    : QEC.Distillation.taggedCczAmplitude_eq_of_agree_on_coordinateSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:12:20.549198+00:00
-- url     : https://prove2.me/theorems/414797b3-39ae-415d-b23c-991918e715d6
-- title:
--   Distillation: tagged Ccz Amplitude eq of agree on coordinate Support
-- statement:
--   The tagged local phase depends only on its declared three-coordinate support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/PhysicalCCZ.lean#L39-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/PhysicalCCZ.lean#L39-L51

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_PhysicalCCZ
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
open scoped BigOperators
universe u
variable {F ι : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
omit [Fintype F]

theorem QEC.Distillation.taggedCczAmplitude_eq_of_agree_on_coordinateSupport
    [Fintype ι] [DecidableEq ι] (site : ι)
    (label label' : TaggedThreeCopyRegisterLabel F ι)
    (h : ∀ coordinate ∈ coordinateSupport site,
      label coordinate = label' coordinate) :
    taggedCczAmplitude site label = taggedCczAmplitude site label' := by sorry

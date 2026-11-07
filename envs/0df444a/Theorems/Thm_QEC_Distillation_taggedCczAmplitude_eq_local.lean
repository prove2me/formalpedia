-- Prove2me | Theorems.Thm_QEC_Distillation_taggedCczAmplitude_eq_local
-- name    : QEC.Distillation.taggedCczAmplitude_eq_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:44:15.654934+00:00
-- url     : https://prove2.me/theorems/3df71331-d2fa-4ca1-9f52-90fd52a95355
-- title:
--   Distillation: tagged Ccz Amplitude eq local
-- statement:
--   The selected tagged phase is exactly the already-defined local CCZ phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Phase.lean#L206-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Phase.lean#L206-L212

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
universe u
variable {F ι : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
omit [Fintype F]

theorem QEC.Distillation.taggedCczAmplitude_eq_local [Fintype ι] [DecidableEq ι]
    (site : ι) (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczAmplitude site label =
      cczAmplitude (label (ThreeCopyTag.first, site))
        (label (ThreeCopyTag.second, site))
        (label (ThreeCopyTag.third, site)) := by sorry

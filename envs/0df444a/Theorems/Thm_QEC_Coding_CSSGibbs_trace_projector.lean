-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_trace_projector
-- name    : QEC.Coding.CSSGibbs.trace_projector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:04:17.108748+00:00
-- url     : https://prove2.me/theorems/69b9d804-a1ef-448c-990f-b3099e74ed46
-- title:
--   CSSGibbs: trace projector
-- statement:
--   The CSSGibbs construction uses the trace projector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L262-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L262-L265

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {κP κQ : Type} [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)

theorem QEC.Coding.CSSGibbs.trace_projector (s : Word (ZMod 2) (Sum κP κQ)) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι) (projector P Q horth s) =
      (Module.finrank ℂ (sector P Q horth s) : ℂ) := by sorry

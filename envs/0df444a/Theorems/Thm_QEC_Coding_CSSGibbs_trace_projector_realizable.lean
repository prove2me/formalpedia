-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_trace_projector_realizable
-- name    : QEC.Coding.CSSGibbs.trace_projector_realizable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:05:42.299764+00:00
-- url     : https://prove2.me/theorems/2ee3a78b-9511-4edb-9110-401800695315
-- title:
--   CSSGibbs: trace projector realizable
-- statement:
--   The CSSGibbs construction uses the trace projector realizable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L309-L318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L309-L318

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

theorem QEC.Coding.CSSGibbs.trace_projector_realizable (u : LinearMap.range P) (v : LinearMap.range Q) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι) (projector P Q horth (joinSyndrome u.val v.val)) =
      LinearMap.trace ℂ (Qubit.QubitRegister ι) (projector P Q horth 0) := by sorry

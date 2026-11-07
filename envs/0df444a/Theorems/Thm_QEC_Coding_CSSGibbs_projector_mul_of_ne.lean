-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_projector_mul_of_ne
-- name    : QEC.Coding.CSSGibbs.projector_mul_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:04:11.854466+00:00
-- url     : https://prove2.me/theorems/59efeb1f-9941-4b9f-aa06-11602e6eff3c
-- title:
--   CSSGibbs: projector mul of ne
-- statement:
--   The CSSGibbs construction uses the projector mul of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L224-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L224-L227

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

theorem QEC.Coding.CSSGibbs.projector_mul_of_ne (s t : Word (ZMod 2) (Sum κP κQ)) (hst : s ≠ t) :
    projector P Q horth s * projector P Q horth t = 0 := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_projector_error_conjugate
-- name    : QEC.Coding.CSSGibbs.projector_error_conjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:05:31.642583+00:00
-- url     : https://prove2.me/theorems/019e09f1-7142-43df-918e-9323c11f2ff5
-- title:
--   CSSGibbs: projector error conjugate
-- statement:
--   Real Pauli conjugation constructs every error-reachable sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L283-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L283-L291

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

theorem QEC.Coding.CSSGibbs.projector_error_conjugate (E : Binary ι) :
    projector P Q horth (stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E) =
      toHermitianQubitOperator E * projector P Q horth 0 * toHermitianQubitOperator E := by sorry

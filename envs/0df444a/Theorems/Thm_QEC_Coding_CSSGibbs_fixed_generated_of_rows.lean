-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_fixed_generated_of_rows
-- name    : QEC.Coding.CSSGibbs.fixed_generated_of_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:05:37.776208+00:00
-- url     : https://prove2.me/theorems/2f66aff8-6aea-4530-9ae5-a6747b8ae382
-- title:
--   CSSGibbs: fixed generated of rows
-- statement:
--   A fixed vector for the rows is fixed by every generated Pauli.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L321-L339
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L321-L339

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

theorem QEC.Coding.CSSGibbs.fixed_generated_of_rows (x : Qubit.QubitRegister ι)
    (hx : ∀ j, toQubitOperator (binaryCSSParityCheckGenerators P Q j) x = x)
    (G : Binary ι) (hG : GeneratedStabilizer (binaryCSSParityCheckGenerators P Q) G) :
    toQubitOperator G x = x := by sorry

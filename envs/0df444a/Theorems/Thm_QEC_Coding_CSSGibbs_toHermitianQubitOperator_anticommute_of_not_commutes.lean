-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_toHermitianQubitOperator_anticommute_of_not_commutes
-- name    : QEC.Coding.CSSGibbs.toHermitianQubitOperator_anticommute_of_not_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:04:14.610851+00:00
-- url     : https://prove2.me/theorems/80bd7c39-4b05-4887-9878-c8a0eb85dfa8
-- title:
--   CSSGibbs: to Hermitian Qubit Operator anticommute of not commutes
-- statement:
--   A signed Hermitian Pauli anticommutes concretely when its binary words do.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L30-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L30-L37

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

theorem QEC.Coding.CSSGibbs.toHermitianQubitOperator_anticommute_of_not_commutes
    (P Q : Binary ι) (h : ¬ Commutes P Q) :
    toHermitianQubitOperator P * toHermitianQubitOperator Q =
      -(toHermitianQubitOperator Q * toHermitianQubitOperator P) := by sorry

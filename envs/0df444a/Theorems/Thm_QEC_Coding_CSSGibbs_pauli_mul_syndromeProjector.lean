-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_pauli_mul_syndromeProjector
-- name    : QEC.Coding.CSSGibbs.pauli_mul_syndromeProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:03:58.731057+00:00
-- url     : https://prove2.me/theorems/c75f9a16-7d72-43d3-b42f-530996df56f4
-- title:
--   CSSGibbs: pauli mul syndrome Projector
-- statement:
--   A Pauli error transports the full joint syndrome projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L136-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L136-L143

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

theorem QEC.Coding.CSSGibbs.pauli_mul_syndromeProjector
    (checks : κ → Binary ι) (hcomm : ∀ a b, Commutes (checks a) (checks b))
    (error : Binary ι) (syndrome : JointSyndrome κ) :
    toHermitianQubitOperator error * jointStabilizerProjector checks hcomm syndrome =
      jointStabilizerProjector checks hcomm (transportSyndrome checks hcomm error syndrome) *
        toHermitianQubitOperator error := by sorry

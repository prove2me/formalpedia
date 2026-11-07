-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_hermitian_cssZ
-- name    : QEC.Coding.CSSGibbs.hermitian_cssZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:04:06.912445+00:00
-- url     : https://prove2.me/theorems/d9043ad4-d210-47fc-9b8c-e98531892634
-- title:
--   CSSGibbs: hermitian css Z
-- statement:
--   The Hermitian correction is trivial on an actual pure Z check.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L181-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L181-L184

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

theorem QEC.Coding.CSSGibbs.hermitian_cssZ (z : Word (ZMod 2) ι) :
    toHermitianQubitOperator (cssZCheck z) = toQubitOperator (cssZCheck z) := by sorry

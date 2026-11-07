-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_hermitian_cssX
-- name    : QEC.Coding.CSSGibbs.hermitian_cssX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:03:53.875199+00:00
-- url     : https://prove2.me/theorems/e831474b-b0e4-444f-beaa-3af4d5bccd4c
-- title:
--   CSSGibbs: hermitian css X
-- statement:
--   The Hermitian correction is trivial on an actual pure X check.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L175-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L175-L178

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

theorem QEC.Coding.CSSGibbs.hermitian_cssX (x : Word (ZMod 2) ι) :
    toHermitianQubitOperator (cssXCheck x) = toQubitOperator (cssXCheck x) := by sorry

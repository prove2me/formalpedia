-- Prove2me | Theorems.Thm_QEC_Coding_ReedMuller_evaluation_pairing_eq_zero_of_add_lt
-- name    : QEC.Coding.ReedMuller.evaluation_pairing_eq_zero_of_add_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:17:23.209495+00:00
-- url     : https://prove2.me/theorems/a5b13604-737f-405e-9089-c67cbbf62566
-- title:
--   Reed Muller: evaluation pairing eq zero of add lt
-- statement:
--   Evaluations of total degree below m are orthogonal on the Boolean cube.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L300-L329
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean#L300-L329

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators

theorem QEC.Coding.ReedMuller.evaluation_pairing_eq_zero_of_add_lt {m r s : Nat}
    (hdegree : r + s < m)
    (left : ANFPolynomial m r) (right : ANFPolynomial m s) :
    wordPairing (evaluationLinearMap m r left)
      (evaluationLinearMap m s right) = 0 := by sorry

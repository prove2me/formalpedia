-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_exists_classicalRightInverse_of_surjective
-- name    : QEC.Coding.DistanceBalancing.exists_classicalRightInverse_of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:17:41.777274+00:00
-- url     : https://prove2.me/theorems/1e00695a-11cf-4704-ba01-c409c1e3ae62
-- title:
--   Distance Balancing: exists classical Right Inverse of surjective
-- statement:
--   Surjectivity of the classical boundary supplies the right inverse used by
--   the slice-filling argument.  In particular, callers do not provide an
--   auxiliary matrix representation or a chosen inverse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1232-L1245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L1232-L1245

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)

theorem QEC.Coding.DistanceBalancing.exists_classicalRightInverse_of_surjective
    (hSurjective : Function.Surjective
      (Matrix.toLin' D.classicalBoundary)) :
    ∃ S : Matrix classicalBit classicalCheck (ZMod 2),
      IsClassicalRightInverse D S := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_matrix_sub_mul_one_add_smul
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.matrix_sub_mul_one_add_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:03:04.703853+00:00
-- url     : https://prove2.me/theorems/2ed25f54-5e1c-41a6-9042-ecc63a0f3d31
-- title:
--   Cartwright Steger: matrix sub mul one add smul
-- statement:
--   Distribute a computed leading term and defect across an explicit
--   `1 + s S` inverse.  This noncommutative identity leaves the scalar outside
--   the matrix products, ready for the cyclic wrap-sum lemma.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L618-L623
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityAction.lean#L618-L623

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.matrix_sub_mul_one_add_smul
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (X N S : Matrix n n K) (s : K) :
    (X - N) * (1 + s • S) =
      X - N + s • (X * S - N * S) := by sorry

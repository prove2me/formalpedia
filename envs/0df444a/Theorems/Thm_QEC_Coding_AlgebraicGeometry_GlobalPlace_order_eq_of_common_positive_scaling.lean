-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_eq_of_common_positive_scaling
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.order_eq_of_common_positive_scaling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:11.444802+00:00
-- url     : https://prove2.me/theorems/8a9586de-1ccc-45a3-ab9d-09f16419df4d
-- title:
--   Global Place: order eq of common positive scaling
-- statement:
--   A normalized order cannot be rescaled by a different positive integer
--   while preserving the same values on a field. Evaluating at both actual
--   uniformizers determines the scaling factor and hence the order itself.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrderTransport.lean#L18-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrderTransport.lean#L18-L49

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.order_eq_of_common_positive_scaling
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P Q : GlobalPlace k K) (e f : ℕ) (he : 0 < e) (hf : 0 < f)
    (h : ∀ x : K, (e : ℤ) * P.order x = (f : ℤ) * Q.order x) :
    P.order = Q.order := by sorry

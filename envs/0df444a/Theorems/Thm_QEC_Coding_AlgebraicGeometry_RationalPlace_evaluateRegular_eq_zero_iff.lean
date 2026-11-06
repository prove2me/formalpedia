-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluateRegular_eq_zero_iff
-- name    : QEC.Coding.AlgebraicGeometry.RationalPlace.evaluateRegular_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:44:21.052889+00:00
-- url     : https://prove2.me/theorems/946e4de9-4dfc-494a-836d-ae43cf2b4cad
-- title:
--   Rational Place: evaluate Regular eq zero iff
-- statement:
--   The regular-function version of the kernel characterization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean#L107-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean#L107-L113

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RationalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.RationalPlace.evaluateRegular_eq_zero_iff (Q : RationalPlace k F) (f : F)
    (hf : GlobalPlace.RegularAt Q.place f) :
    Q.evaluateRegular f hf = 0 ↔
      (⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩ :
        GlobalPlace.valuationRing Q.place) ∈
        IsLocalRing.maximalIdeal (GlobalPlace.valuationRing Q.place) := by sorry

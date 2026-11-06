-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_integralClosurePlace_order_algebraMap
-- name    : QEC.Coding.AlgebraicGeometry.integralClosurePlace_order_algebraMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:27:06.534356+00:00
-- url     : https://prove2.me/theorems/70d48e01-3ffc-489a-abf5-f6fe7966baf9
-- title:
--   Algebraic Geometry: integral Closure Place order algebra Map
-- statement:
--   Normalized order at the place defined by a supplied height-one
--   contraction scales lower nonzero elements by its ramification index.  This is
--   the regular arm's zero-correction transport; it is proved from the supplied
--   contraction, not assumed as a selected-place property.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/IntegralClosureOrder.lean#L157-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/IntegralClosureOrder.lean#L157-L238

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Mathlib.NumberTheory.RamificationInertia.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.integralClosurePlace_order_algebraMap
    {K L : Type*} [_root_.Field K] [_root_.Field L] [Algebra k K]
    [Algebra k L] [Algebra K L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [hDedekind : IsDedekindDomain
      (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    (H : IsDedekindDomain.HeightOneSpectrum
      (integralClosure P.valuationRing L))
    (y : K) (hy : y ≠ 0) :
    (integralClosurePlace (k := k) H).order
        (algebraMap K L y) =
      ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' H.asIdeal : ℤ) *
        P.order y := by sorry

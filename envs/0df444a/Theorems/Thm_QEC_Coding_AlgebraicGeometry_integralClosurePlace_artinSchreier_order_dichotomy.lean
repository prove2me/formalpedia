-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_integralClosurePlace_artinSchreier_order_dichotomy
-- name    : QEC.Coding.AlgebraicGeometry.integralClosurePlace_artinSchreier_order_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:51:25.157445+00:00
-- url     : https://prove2.me/theorems/66482745-3e8b-4480-99bc-bad793f7ebed
-- title:
--   Algebraic Geometry: integral Closure Place artin Schreier order dichotomy
-- statement:
--   At any specified prime of a genuine degree-two extension, the literal
--   Artin--Schreier equation preserves the normalized-pole/regular alternative.
--   Order compatibility and the ramification bound are derived here from the
--   prime and the field degree; the caller supplies only the equation and the
--   lower order, as in the basic edges of Property (A).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/IntegralClosureOrder.lean#L246-L284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/IntegralClosureOrder.lean#L246-L284

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Mathlib.NumberTheory.RamificationInertia.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.integralClosurePlace_artinSchreier_order_dichotomy
    {K L : Type*} [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [Algebra.IsSeparable K L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    (H : IsDedekindDomain.HeightOneSpectrum
      (integralClosure P.valuationRing L))
    [H.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.valuationRing)]
    (hdegree : Module.finrank K L = 2)
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (ha : P.order a = -1 ∨ 0 ≤ P.order a) :
    (integralClosurePlace (k := k) H).order y = -1 ∨
      0 ≤ (integralClosurePlace (k := k) H).order y := by sorry

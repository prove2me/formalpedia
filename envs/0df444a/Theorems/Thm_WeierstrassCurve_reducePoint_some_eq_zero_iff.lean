-- Prove2me | Theorems.Thm_WeierstrassCurve_reducePoint_some_eq_zero_iff
-- name    : WeierstrassCurve.reducePoint_some_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/dc6055ef-6a65-5c41-9d4e-0c7d06f343ee
-- title:
--   Affine point reduces to O iff x is non-integral
-- statement:
--   Let $R$ be a discrete valuation ring that is a domain, let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$, and let $W$ be a Weierstrass curve over $K$ carrying an instance of the predicate `WeierstrassCurve.HasGoodReduction` for $R$. Let $x, y \in K$ satisfy `W.toAffine.Nonsingular x y`, i.e. $(x,y)$ is a nonsingular affine point of $W$. Write $v$ for the valuation on $K$ attached to the maximal ideal of $R$ as a height-one prime of $R$, in the multiplicative normalisation, and let `reducePoint_alt` be the reduction map on affine points, which sends the point at infinity to the point at infinity and sends a nonsingular affine point $(x,y)$ to the point with coordinates `reduceCoord R x`, `reduceCoord R y` on the reduced curve `W.reduction R` when $v(x) \le 1$, $v(y) \le 1$ and that pair is a nonsingular point of the reduced curve, and to the point at infinity in all remaining cases (here `reduceCoord R x` is the residue in the residue field of $R$ of a chosen preimage of $x$ in $R$ when one exists, and $0$ otherwise). The assertion is that `reducePoint_alt R W (.some x y h)` equals the point at infinity if and only if $v(x) \le 1$ fails.
--
--   This identifies the kernel of reduction on affine points: a nonsingular affine point of a curve with good reduction over a discrete valuation ring reduces to the point at infinity exactly when its $x$-coordinate is not integral, so the points of the formal group are precisely those with a pole in $x$. It is used in the study of reduction of points, in particular in the construction of specialisation homomorphisms and in the proof that the Galois representation attached to a curve with good reduction is unramified at the relevant place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_reducePoint_some_eq_zero_iff.lean

import Mathlib
import Definitions.Def_EllipticCurve_PointReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.reducePoint_some_eq_zero_iff
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.HasGoodReduction R] {x y : K} (h : W.toAffine.Nonsingular x y) :
    WeierstrassCurve.reducePoint_alt R W (.some x y h) = .zero ↔
      ¬ IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1 := by sorry

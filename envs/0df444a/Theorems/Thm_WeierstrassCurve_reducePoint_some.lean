-- Prove2me | Theorems.Thm_WeierstrassCurve_reducePoint_some
-- name    : WeierstrassCurve.reducePoint_some
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/6811c24a-05be-5b4a-b485-5b5364653347
-- title:
--   Reduction of an integral affine point has residue coordinates
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, $K$ a field equipped with an $R$-algebra structure making it a fraction field of $R$, and $W$ a Weierstrass curve over $K$ satisfying `HasGoodReduction R`. Let $x,y \in K$ together with a proof $h$ that $(x,y)$ is a nonsingular point of the affine curve attached to $W$, and suppose that the $\mathrm{maximalIdeal}\ R$-adic valuation on $K$ satisfies $v(x) \le 1$ and $v(y) \le 1$, i.e. both coordinates are integral. The conclusion asserts the existence of a proof $h'$ that $(\mathrm{reduceCoord}\ R\ x, \mathrm{reduceCoord}\ R\ y)$ is a nonsingular point of the reduced curve `W.reduction R` over the residue field of $R$, such that `reducePoint_alt R W` applied to the affine point `.some x y h` equals the affine point `.some` with these two coordinates and witness $h'$. Here $\mathrm{reduceCoord}\ R\ z$ is the residue in the residue field of some $r \in R$ with $\mathrm{algebraMap}\ R\ K\ r = z$ when such $r$ exists, and $0$ otherwise; and `reducePoint_alt` is defined by cases, sending `.some x y _` to the point with reduced coordinates when both valuations are $\le 1$ and the reduced pair is nonsingular, and to the zero point otherwise.
--
--   This is the specification lemma for the reduction map $W(K) \to \tilde W(k)$ on points with integral coordinates: on such a point the map is given by reducing the coordinates, and no branch of the case distinction in its definition is taken trivially. It is used in the construction of specialisation homomorphisms on points and in the proof that the Galois representation attached to a curve with good reduction at a place is unramified there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_reducePoint_some.lean

import Mathlib
import Definitions.Def_EllipticCurve_PointReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.reducePoint_some
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.HasGoodReduction R] {x y : K} (h : W.toAffine.Nonsingular x y)
    (hx : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1)
    (hy : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) y ≤ 1) :
    ∃ h', WeierstrassCurve.reducePoint_alt R W (.some x y h)
      = .some (WeierstrassCurve.reduceCoord R x) (WeierstrassCurve.reduceCoord R y) h' := by sorry

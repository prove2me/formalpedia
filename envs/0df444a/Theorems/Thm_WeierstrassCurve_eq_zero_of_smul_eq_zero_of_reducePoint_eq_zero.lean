-- Prove2me | Theorems.Thm_WeierstrassCurve_eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero
-- name    : WeierstrassCurve.eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/a540f792-5d03-5254-bd77-f2b0a6c475a3
-- title:
--   Reduction is injective on n-torsion, n invertible in the residue field
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain that is an `IsDiscreteValuationRing`) with fraction field $K$, and let $W$ be a Weierstrass curve over $K$ carrying the good-reduction hypothesis `W.HasGoodReduction R` (which in particular supplies the minimality over $R$ needed to form the reduced curve `W.reduction R` over the residue field of $R$). Let $n$ be a natural number whose image in `IsLocalRing.ResidueField R` is nonzero, and let $P$ be a point of the affine curve `W.toAffine`, i.e. either the point at infinity or a pair $(x,y)$ of elements of $K$ satisfying the nonsingular affine equation. Assume $n \cdot P = 0$ in the group of affine points, and that [`WeierstrassCurve.reducePoint_alt R W P = 0`](def/EllipticCurve_PointReduction.html#L22), i.e. $P$ dies under the reduction map which sends the point at infinity to the point at infinity, and sends an affine point $(x,y)$ to the point with coordinates $(\overline{x},\overline{y})$ — each coordinate being the residue of a chosen $R$-preimage when one exists and $0$ otherwise — provided both coordinates have valuation at most $1$ in the normalisation used and the resulting pair is nonsingular on `W.reduction R`, and to the point at infinity in every other case. Then $P = 0$.
--
--   This is the injectivity of reduction on torsion of order prime to the residue characteristic (Silverman, Arithmetic of Elliptic Curves, VII.3.1(b)), here in the form that a point killed by such an $n$ and lying in the kernel of reduction is trivial. It is used downstream for the comparison of $K$-rational torsion with points of the reduced curve and for the construction of specialisation homomorphisms on torsion, and hence in the handling of level structures on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero.lean

import Mathlib
import Definitions.Def_EllipticCurve_PointReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.HasGoodReduction R] {n : ℕ} (hn : (n : IsLocalRing.ResidueField R) ≠ 0)
    (P : W.toAffine.Point) (hP : n • P = 0) (h0 : WeierstrassCurve.reducePoint_alt R W P = 0) :
    P = 0 := by sorry

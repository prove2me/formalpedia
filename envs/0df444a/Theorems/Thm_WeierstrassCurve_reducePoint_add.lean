-- Prove2me | Theorems.Thm_WeierstrassCurve_reducePoint_add
-- name    : WeierstrassCurve.reducePoint_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/25dc37b9-1395-5558-9697-afa461c46bea
-- title:
--   Reduction of points is additive under good reduction
-- statement:
--   Let $R$ be a discrete valuation ring that is a domain, and let $K$ be a field which is a fraction field of $R$ (with the residue field of $R$ and $K$ carrying decidable equality). Let $W$ be a Weierstrass curve over $K$ satisfying the predicate `WeierstrassCurve.HasGoodReduction` for $R$, so that in particular $W$ is minimal over $R$ and has a reduction `W.reduction R` over the residue field. For points $P$ and $Q$ of the affine group $W(K)$ given by the chord–tangent law, the assertion is that the map [`WeierstrassCurve.reducePoint_alt R W`](def/EllipticCurve_PointReduction.html#L22) from $W(K)$ to the points of the reduced curve commutes with addition: the reduction of $P+Q$ equals the sum of the reductions of $P$ and of $Q$. Here `reducePoint_alt` sends the point at infinity to the point at infinity, and sends an affine point $(x,y)$ to the affine point with coordinates `reduceCoord R x`, `reduceCoord R y` — the residue classes of chosen preimages in $R$ of $x$ and $y$, and $0$ when no preimage exists — provided both $x$ and $y$ have valuation at most $1$ at the maximal ideal of $R$ and the resulting pair is nonsingular on the reduced curve, and to the point at infinity in all other cases. Thus the conclusion says that this map is additive, without asserting it is a group homomorphism bundled as such.
--
--   This is the classical statement that reduction $W(K) \to \widetilde{W}(k)$ is a group homomorphism in the case of good reduction (Silverman, Ch. VII, Prop. 2.1), here in the form of additivity of the explicitly defined reduction map on points. It is used downstream to obtain specialisation homomorphisms on points, divisibility of the order of a torsion point by the reduced group's cardinality, and compatibility of level structures on modular curves with reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_reducePoint_add.lean

import Mathlib
import Definitions.Def_EllipticCurve_PointReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.reducePoint_add
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    [DecidableEq (IsLocalRing.ResidueField R)]
    (W : WeierstrassCurve K) [W.HasGoodReduction R] (P Q : W.toAffine.Point) :
    WeierstrassCurve.reducePoint_alt R W (P + Q)
      = WeierstrassCurve.reducePoint_alt R W P + WeierstrassCurve.reducePoint_alt R W Q := by sorry

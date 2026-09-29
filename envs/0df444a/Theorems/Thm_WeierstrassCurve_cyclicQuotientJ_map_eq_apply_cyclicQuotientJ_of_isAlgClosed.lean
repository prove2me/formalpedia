-- Prove2me | Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed
-- name    : WeierstrassCurve.cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/7b18198e-6863-5196-9b95-a145899c8d18
-- title:
--   Naturality of the cyclic-quotient j-invariant under field maps
-- statement:
--   Let $L$ and $L'$ be fields with decidable equality, with $L$ algebraically closed, let $\sigma : L \to L'$ be a ring homomorphism, let $V$ be a Weierstrass curve over $L$, let $H$ be an additive subgroup of the group $V(L)$ of points of the associated affine curve `V.toAffine`, and let $N$ be a natural number. On one side, form the Weierstrass curve `V.map σ` over $L'$ obtained by applying $\sigma$ to the coefficients of $V$, and the image of $H$ under [`WeierstrassCurve.mapPointHom σ`](def/WeierstrassCurve_MapPoint.html#L57), the additive homomorphism $V(L) \to (V.\mathrm{map}\,\sigma)(L')$ that fixes the point at infinity and sends an affine point $(x,y)$ to $(\sigma x, \sigma y)$. The assertion is that the cyclic-quotient invariant of `V.map σ` relative to this image subgroup and $N$ coincides with the image under $\sigma$ of the cyclic-quotient invariant of $V$ relative to $H$ and $N$. Here `cyclicQuotientJ` of a curve, a subgroup and $N$ is the quantity $c_4^3/\Delta$ computed on the curve `cyclicQuotientCurve` produced by the iterative construction `cqjIterate`, a generator-free, totally defined $N$-step quotient construction.
--
--   This is the naturality (Galois- and, in particular, Frobenius-equivariance) statement for the $j$-invariant of the quotient of a Weierstrass curve by a subgroup of its points, with the source field algebraically closed. It is used in the analysis of the $j$-invariants attached to Tate points and level structures on modular curves, where quotient $j$-invariants must be compared before and after reduction or after applying a field automorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_MapPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem WeierstrassCurve.cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed
    {L : Type u} {L' : Type v} [Field L] [Field L'] [DecidableEq L] [DecidableEq L'] [IsAlgClosed L] (σ : L →+* L')
    (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    (V.map σ).cyclicQuotientJ (H.map (WeierstrassCurve.mapPointHom σ)) N = σ (V.cyclicQuotientJ H N) := by sorry

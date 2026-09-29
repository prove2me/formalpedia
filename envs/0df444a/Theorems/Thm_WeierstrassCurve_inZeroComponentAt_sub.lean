-- Prove2me | Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub
-- name    : WeierstrassCurve.inZeroComponentAt_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/d1c504c9-b8d6-5d09-ba1b-6d5d3f4d5019
-- title:
--   The zero component at A is closed under subtraction
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, and let $P,Q$ be points of the base change to $\overline{\mathbb{Q}}$ of the Weierstrass curve $W$ viewed over $\mathbb{Q}$ via the canonical ring homomorphism $\mathbb{Z}\to\mathbb{Q}$, in the sense of the affine point group of that curve. The predicate [`WeierstrassCurve.InZeroComponentAt`](def/EllipticCurve_ZeroComponentAt.html#L13) for $W$, $A$ and a point $P$ asserts that either $P=0$, or there are $x,y\in\overline{\mathbb{Q}}$ together with a proof that $(x,y)$ is a nonsingular point of the associated affine curve, such that $P$ is the affine point with coordinates $x,y$ and, in addition, either $x\notin A$, or else $x\in A$, $y\in A$ and the images of $x$ and $y$ under the residue map of $A$ form a nonsingular point of the Weierstrass curve obtained from $W$ by reducing its coefficients to the residue field of $A$. The theorem states that if $P$ and $Q$ both satisfy this predicate, then so does $P-Q$, the difference taken in the group of points. No hypothesis is imposed on the discriminant of $W$ or on its reduction behaviour at $A$.
--
--   This is the statement that the zero component at a place $A$, consisting of the origin together with the points whose abscissa is not $A$-integral and the $A$-integral points with nonsingular reduction, is stable under subtraction, so that it is a subgroup of the group of $\overline{\mathbb{Q}}$-points; classically this is the assertion that $E_0(K)$ is a subgroup, reduction to the smooth locus of the reduced cubic being a homomorphism. It is used in the construction of filtrations at a prime for curves with multiplicative reduction and, through these, in the analysis of the points of the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_inZeroComponentAt_sub.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.inZeroComponentAt_sub
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {P Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point}
    (hP : W.InZeroComponentAt A P) (hQ : W.InZeroComponentAt A Q) :
    W.InZeroComponentAt A (P - Q) := by sorry

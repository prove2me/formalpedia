-- Prove2me | Theorems.Thm_WeierstrassCurve_inZeroComponentAt_of_isGoodPrimeFor
-- name    : WeierstrassCurve.inZeroComponentAt_of_isGoodPrimeFor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/c7358dc7-bda5-51f4-8541-2b8961d8cacf
-- title:
--   Good reduction: all ℚ̄-points lie in the zero component
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb Z$, let $\ell$ be a prime number, and assume $W$ is a good prime for $\ell$ in the sense that $(\ell : \mathbb Z)$ does not divide the discriminant $W.\Delta$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $\ell$, meaning that the image of $\ell$ in $\overline{\mathbb Q}$ belongs to the nonunits of $A$, i.e. to its maximal ideal. Let $P$ be a point of the base change to $\overline{\mathbb Q}$ of the Weierstrass curve obtained from $W$ by mapping its coefficients along $\mathbb Z \to \mathbb Q$. Then $P$ lies in the zero component at $A$, which by definition means: either $P = 0$, or $P$ is an affine point $(x,y)$ with $x, y \in \overline{\mathbb Q}$ nonsingular on the affine model, such that either $x \notin A$, or else $x \in A$ and $y \in A$ and the pair of residues of $x$ and $y$ in the residue field of $A$ is a nonsingular point of the Weierstrass curve obtained from $W$ by reducing its coefficients into that residue field.
--
--   This is the statement that at a prime of good reduction for the integral model the zero component coincides with the whole group of $\overline{\mathbb Q}$-points, so that reduction at a place above $\ell$ is defined on all points (Silverman, AEC VII.2, VII.5). It is used in the analysis of torsion and Frobenius at good primes, notably by [`WeierstrassCurve.exists_torsionBy_linearEquiv_residueField_of_isFrobeniusAt`](thm.html#WeierstrassCurve.exists_torsionBy_linearEquiv_residueField_of_isFrobeniusAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_inZeroComponentAt_of_isGoodPrimeFor.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.inZeroComponentAt_of_isGoodPrimeFor (W : WeierstrassCurve ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hgood : W.IsGoodPrimeFor ℓ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) : W.InZeroComponentAt A P := by sorry

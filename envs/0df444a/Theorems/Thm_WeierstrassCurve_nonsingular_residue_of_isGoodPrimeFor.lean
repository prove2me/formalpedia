-- Prove2me | Theorems.Thm_WeierstrassCurve_nonsingular_residue_of_isGoodPrimeFor
-- name    : WeierstrassCurve.nonsingular_residue_of_isGoodPrimeFor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/081796c5-054b-50a7-b6fe-530e8788f27a
-- title:
--   Good reduction: integral solutions reduce to nonsingular points
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, given by coefficients $a_1,a_2,a_3,a_4,a_6 \in \mathbb{Z}$, and let $\ell$ be a prime natural number such that $\ell$ is a good prime for $W$, meaning that $\ell$, viewed in $\mathbb{Z}$, does not divide the discriminant $\Delta(W)$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $\ell$, that is, the image of $\ell$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$ (so it lies in the maximal ideal of $A$). Let $x, y \in \overline{\mathbb{Q}}$ be a solution of the affine Weierstrass equation of the base change to $\overline{\mathbb{Q}}$ of the curve $W$ pushed forward along $\mathbb{Z} \to \mathbb{Q}$, and suppose that both $x$ and $y$ belong to $A$. Then, writing $k_A$ for the residue field of the local ring $A$ and $\overline{W}$ for the Weierstrass curve over $k_A$ obtained from $W$ by reducing its coefficients along $\mathbb{Z} \to k_A$, the point whose coordinates are the residues of $x$ and $y$ in $k_A$ is a nonsingular point of the affine curve $\overline{W}$.
--
--   This is the pointwise statement that at a prime of good reduction for the chosen integral model, the reduction of a solution with coordinates integral at a place above $\ell$ is a smooth point of the reduced curve (Silverman, AEC VII.2, VII.5). It feeds the explicit analysis of reduction at good primes, being used for the comparison of torsion with points over the residue field at a Frobenius place and for the statement that such reductions lie in the identity component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_nonsingular_residue_of_isGoodPrimeFor.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.nonsingular_residue_of_isGoodPrimeFor (W : WeierstrassCurve ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hgood : W.IsGoodPrimeFor ℓ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) {x y : AlgebraicClosure ℚ} (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Equation x y) (hx : x ∈ A) (hy : y ∈ A) : (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.Nonsingular (IsLocalRing.residue A ⟨x, hx⟩) (IsLocalRing.residue A ⟨y, hy⟩) := by sorry

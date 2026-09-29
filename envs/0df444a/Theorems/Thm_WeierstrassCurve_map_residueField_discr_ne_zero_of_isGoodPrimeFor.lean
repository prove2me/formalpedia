-- Prove2me | Theorems.Thm_WeierstrassCurve_map_residueField_discr_ne_zero_of_isGoodPrimeFor
-- name    : WeierstrassCurve.map_residueField_discr_ne_zero_of_isGoodPrimeFor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/5ffd9160-2303-5950-90e4-8410a26d2a09
-- title:
--   Good reduction at ℓ: discriminant nonzero in the residue field
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, i.e. a tuple of coefficients $a_1,a_2,a_3,a_4,a_6 \in \mathbb{Z}$, and let $\ell$ be a prime number such that $\ell$ is a good prime for $W$ in the sense that the integer $\ell$ does not divide the discriminant $\Delta(W) \in \mathbb{Z}$. Let $A$ be a valuation subring of the algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$ which lies over $\ell$, meaning that the image of $\ell$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$, i.e. lies in the maximal ideal of $A$. Write $k_A$ for the residue field of the local ring $A$. Then the Weierstrass curve over $k_A$ obtained from $W$ by pushing its coefficients along the composite ring homomorphism $\mathbb{Z} \to k_A$ has nonzero discriminant: $\Delta\bigl(W \otimes k_A\bigr) \neq 0$ in $k_A$.
--
--   This is the elementary half of the statement that a prime $\ell$ not dividing the discriminant of an integral Weierstrass model is a prime of good reduction: the reduced model over the residue field of a place of $\overline{\mathbb{Q}}$ above $\ell$ is again nonsingular. It is used in the project to know that the special fibre at $\ell$ is an elliptic curve, and is cited by the statements on nonsingularity of the reduction, on torsion valuations, and on the $\ell$-torsion of the reduced curve at a Frobenius place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_map_residueField_discr_ne_zero_of_isGoodPrimeFor.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.map_residueField_discr_ne_zero_of_isGoodPrimeFor (W : WeierstrassCurve ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hgood : W.IsGoodPrimeFor ℓ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) : (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).Δ ≠ 0 := by sorry

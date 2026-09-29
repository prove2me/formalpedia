-- Prove2me | Theorems.Thm_WeierstrassCurve_valuation_torsion_of_coeff_prePsi_dvd
-- name    : WeierstrassCurve.valuation_torsion_of_coeff_prePsi_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/708fba36-90dc-5139-af74-4949489ff98f
-- title:
--   Valuations of p-torsion under supersingular coefficient condition
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and let $p$ be a prime with $p \neq 2$. Assume $W$ is good at $p$ in the sense that $p \nmid \Delta(W)$ in $\mathbb{Z}$, and assume the coefficient condition that $p$ divides the $i$-th coefficient of the integral division polynomial $W.\mathrm{pre}\Psi'\,p$ for every $i$ with $1 \le i < (p^{2}-1)/2$ (natural-number division). Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$, meaning that the image of $p$ in $\overline{\mathbb{Q}}$ is a nonunit of $A$, and write $v$ for the valuation attached to $A$. Let $x, y \in \overline{\mathbb{Q}}$ be such that $(x,y)$ is a nonsingular point of the affine model of the base change of $W$ to $\overline{\mathbb{Q}}$ (via $\mathbb{Z} \to \mathbb{Q}$ and then to $\overline{\mathbb{Q}}$), and suppose the corresponding point $P = (x,y)$ of the group of points satisfies $p \cdot P = 0$. Then $v(x)^{(p^{2}-1)/2}\,v(p) = 1$ and $v(y)^{2} = v(x)^{3}$ in the value group of $A$.
--
--   Multiplicatively written, the two identities say that $v_p(x) = -2/(p^{2}-1)$ and $v_p(y) = -3/(p^{2}-1)$ for a $p$-torsion point of a curve whose reduction at $p$ is supersingular (the coefficient hypothesis on $\mathrm{pre}\Psi'\,p$ encoding supersingularity), as in Serre's analysis of the Galois action on torsion points. It feeds the construction of an inertia eigenvector for the tame character in the residual representation and the determination of the supersingular shape of the Galois representation at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_valuation_torsion_of_coeff_prePsi_dvd.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.valuation_torsion_of_coeff_prePsi_dvd (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hgood : W.IsGoodPrimeFor p)
    (hss : ∀ i, 1 ≤ i → i < (p ^ 2 - 1) / 2 → (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (x y : AlgebraicClosure ℚ)
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hP : p • (Point.some x y h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0) :
    A.valuation x ^ ((p ^ 2 - 1) / 2) * A.valuation (p : AlgebraicClosure ℚ) = 1 ∧
      A.valuation y ^ 2 = A.valuation x ^ 3 := by sorry

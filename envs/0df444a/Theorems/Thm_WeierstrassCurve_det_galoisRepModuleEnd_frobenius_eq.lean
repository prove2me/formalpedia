-- Prove2me | Theorems.Thm_WeierstrassCurve_det_galoisRepModuleEnd_frobenius_eq
-- name    : WeierstrassCurve.det_galoisRepModuleEnd_frobenius_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/5744ff86-a304-50fb-9ce2-a8467e0f13e8
-- title:
--   Determinant of ρ̄_{E,p} at a Frobenius is ℓ
-- statement:
--   Let $E$ be a Weierstrass curve over $\mathbf{Q}$ which is elliptic, let $p$ and $\ell$ be primes with $\ell \neq p$, and let $A$ be a valuation subring of $\overline{\mathbf{Q}} =$ `AlgebraicClosure ℚ` which lies over $\ell$, in the sense that $\ell$, viewed in $\overline{\mathbf{Q}}$, is a nonunit of $A$. Let $\sigma$ be an automorphism of $\overline{\mathbf{Q}}$ over $\mathbf{Q}$ which is a Frobenius at $A$ for $\ell$: $\sigma$ belongs to the decomposition subgroup of $A$ over $\mathbf{Q}$, and the induced action of $\sigma$ on the residue field of $A$ is $x \mapsto x^{\ell}$. Consider the $p$-torsion submodule $\mathrm{torsionBy}\ \mathbf{Z}\ (E_{\overline{\mathbf{Q}}})(\overline{\mathbf{Q}})\ p$ of the group of affine points of the base change of $E$ to $\overline{\mathbf{Q}}$, a module over $\mathbf{Z}/p$, and the $\mathbf{Z}/p$-linear endomorphism of it obtained from the Galois action of $\sigma$ by `galoisRepModuleEnd`. The assertion is that the determinant of this endomorphism equals the image of $\ell$ in $\mathbf{Z}/p$.
--
--   This is the identification of $\det\bar\rho_{E,p}$ with the mod $p$ cyclotomic character, evaluated at a Frobenius element above a prime $\ell \neq p$; it follows from the Galois equivariance and nondegeneracy of the Weil pairing on $E[p]$, for which no hypothesis of good reduction at $\ell$ is required. It supplies the determinant datum used in the study of the mod $p$ representations attached to elliptic curves, and is cited in the construction of Frobenius data for good primes and in the realisation of congruences between curves and eigenforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_det_galoisRepModuleEnd_frobenius_eq.lean

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.det_galoisRepModuleEnd_frobenius_eq
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    LinearMap.det (galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ E p σ) = (ℓ : ZMod p) := by sorry

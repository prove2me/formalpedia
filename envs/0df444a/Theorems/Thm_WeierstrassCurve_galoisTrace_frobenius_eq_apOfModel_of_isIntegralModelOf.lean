-- Prove2me | Theorems.Thm_WeierstrassCurve_galoisTrace_frobenius_eq_apOfModel_of_isIntegralModelOf
-- name    : WeierstrassCurve.galoisTrace_frobenius_eq_apOfModel_of_isIntegralModelOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/0e6fff71-d3c8-503b-9183-baa1250cfe6c
-- title:
--   Frobenius trace on E[p] equals a_ℓ mod p
-- statement:
--   Let $E$ be a Weierstrass curve over $\mathbf{Q}$ which is elliptic, and let $W$ be a Weierstrass curve over $\mathbf{Z}$ that is an integral model of $E$, meaning that there is a variable change $C$ over $\mathbf{Q}$ with $C \cdot E$ equal to the base change of $W$ along $\mathbf{Z} \to \mathbf{Q}$. Let $p$ and $\ell$ be primes with $\ell \neq p$, and suppose $\ell$ is a good prime for $W$ in the sense that $(\ell : \mathbf{Z})$ does not divide the discriminant $\Delta_W$. Let $A$ be a valuation subring of $\overline{\mathbf{Q}} =$ `AlgebraicClosure ℚ` lying over $\ell$, i.e. the image of $\ell$ in $\overline{\mathbf{Q}}$ is a non-unit of $A$, and let $\sigma$ be a $\mathbf{Q}$-algebra automorphism of $\overline{\mathbf{Q}}$ which is a Frobenius at $A$ for $\ell$: $\sigma$ belongs to the decomposition subgroup of $A$ over $\mathbf{Q}$ and acts on the residue field of $A$ by $x \mapsto x^{\ell}$. The conclusion is that `galoisTrace ℚ E p σ`, the $\mathbf{Z}/p$-linear trace of the endomorphism induced by $\sigma$ on the $p$-torsion submodule `Submodule.torsionBy ℤ` of the group of affine points of $E$ base changed to $\overline{\mathbf{Q}}$, equals the image in $\mathbf{Z}/p$ of $a_\ell(W) = \#\mathbf{F}_\ell + 1 - \#\widetilde{W}(\mathbf{F}_\ell)$, the trace of Frobenius of the reduction of $W$ modulo $\ell$.
--
--   This is the Eichler–Shimura-type congruence identifying the trace of a Frobenius element on the mod $p$ representation attached to $E$ with the $\ell$-th Frobenius trace of an integral model, stated for an arbitrary integral model rather than only for the curve in Weierstrass form over $\mathbf{Z}$. It is the Frobenius-trace input of the curve-side torsion data used later, being cited in the construction of level-lowering congruences and of good primes distinguishing Frobenius traces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_galoisTrace_frobenius_eq_apOfModel_of_isIntegralModelOf.lean

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.galoisTrace_frobenius_eq_apOfModel_of_isIntegralModelOf
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hgood : W.IsGoodPrimeFor ℓ) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    galoisTrace (K := AlgebraicClosure ℚ) ℚ E p σ = ((W.apOfModel ℓ : ℤ) : ZMod p) := by sorry

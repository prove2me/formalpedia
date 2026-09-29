-- Prove2me | Theorems.Thm_WeierstrassCurve_tateModuleRep_charpoly_frobenius
-- name    : WeierstrassCurve.tateModuleRep_charpoly_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/8f4634d9-5aa8-53ac-b6f3-426deb1a8659
-- title:
--   Frobenius characteristic polynomial on the p-adic Tate module
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and $p$ a prime, and assume that for every $n$ the $p^n$-torsion subgroup of the group of points of the base change of $W$ to $\overline{\mathbb{Q}}$ (via $\mathbb{Z} \to \mathbb{Q}$) has cardinality $(p^n)^2$; this is the hypothesis under which the rank-two $\mathbb{Z}_p$-representation `tateModuleRep` of the absolute Galois group $\operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ on the Tate module — sequences $(x_n)$ of points with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ — is formed. Let $\ell$ be a prime with $\ell \ne p$ and with $\ell \nmid \Delta(W)$ in $\mathbb{Z}$ (`IsGoodPrimeFor`), let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ such that $\ell$ is a non-unit of $A$, and let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ lying in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$. Then the characteristic polynomial of the $\mathbb{Z}_p$-linear endomorphism by which $\sigma$ acts on the Tate module is $X^2 - C(a_\ell)X + C(\ell)$ in $\mathbb{Z}_p[X]$, where $a_\ell$ is the integer $\ell + 1 - \#\big(W \bmod \ell\big)(\mathbb{Z}/\ell)$ attached to the model $W$ by `apOfModel`, and both $a_\ell$ and $\ell$ are cast into $\mathbb{Z}_p$.
--
--   This is the Eichler–Shimura style description of Frobenius on the $p$-adic Tate module of an elliptic curve at a prime of good reduction: trace $a_\ell$ and determinant $\ell$. It is what ties the Galois representation attached to a Frobenius curve to the $L$-series coefficients of its reduction, and it feeds the modularity and level-lowering steps of the argument, in particular the comparison of the Tate-module representation with the one coming from a modular form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_tateModuleRep_charpoly_frobenius.lean

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.LinearAlgebra.Charpoly.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

theorem WeierstrassCurve.tateModuleRep_charpoly_frobenius
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hgood : W.IsGoodPrimeFor ℓ) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    LinearMap.charpoly (((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).ρ σ)
      = X ^ 2 - C ((W.apOfModel ℓ : ℤ) : ℤ_[p]) * X + C ((ℓ : ℕ) : ℤ_[p]) := by sorry

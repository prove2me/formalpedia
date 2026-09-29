-- Prove2me | Theorems.Thm_WeierstrassCurve_tateModuleRep_det_frobenius
-- name    : WeierstrassCurve.tateModuleRep_det_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/991b63b4-ae92-57e7-88fd-6a81189d203f
-- title:
--   Determinant of Frobenius at ℓ ≠ p on the Tate module
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Q}$ and $p$ a prime. Assume $W.\Delta \neq 0$ and assume the counting hypothesis that for every $n$ the subgroup of points of $W$ over $\overline{\mathbb{Q}}$ annihilated by $p^{n}$ has cardinality $(p^{n})^{2}$; these are exactly the data from which the rank-two $p$-adic Galois representation [`WeierstrassCurve.tateModuleRep`](def/EllipticCurve_TateModule.html#L851) is formed, its underlying module being the group of sequences $(x_{n})$ of points with $p^{n} \cdot x_{n} = 0$ and $p \cdot x_{n+1} = x_{n}$, free of rank $2$ over $\mathbb{Z}_{p}$, with the Galois action induced from the action on points. Let $\ell$ be a prime with $\ell \neq p$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ such that the image of $\ell$ lies in the nonunits of $A$, and let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ which lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x \mapsto x^{\ell}$. Then the determinant of the $\mathbb{Z}_{p}$-linear endomorphism by which $\sigma$ acts on the Tate module equals $\ell$ in $\mathbb{Z}_{p}$. Nothing is asserted about the trace, the characteristic polynomial, the case $\ell = p$, or reduction type at $\ell$.
--
--   This is the determinant half of the Eichler–Shimura type description of Frobenius on the $p$-adic Tate module of an elliptic curve: the determinant is the $p$-adic cyclotomic character, whose value at a Frobenius at $\ell$ is $\ell$. It feeds into [`WeierstrassCurve.tateModuleRep_charpoly_frobenius`](thm.html#WeierstrassCurve.tateModuleRep_charpoly_frobenius), where together with the trace it identifies the characteristic polynomial of Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_tateModuleRep_det_frobenius.lean

import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.LinearAlgebra.Determinant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

theorem WeierstrassCurve.tateModuleRep_det_frobenius
    (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ
      (W⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    LinearMap.det ((W.tateModuleRep p hcard).ρ σ) = (ℓ : ℤ_[p]) := by sorry

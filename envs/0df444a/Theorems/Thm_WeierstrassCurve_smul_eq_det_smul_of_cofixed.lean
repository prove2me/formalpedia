-- Prove2me | Theorems.Thm_WeierstrassCurve_smul_eq_det_smul_of_cofixed
-- name    : WeierstrassCurve.smul_eq_det_smul_of_cofixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/8e2a28ee-6ab5-5126-b943-1da5578f1b67
-- title:
--   Galois acts on a proper cofixed submodule of E[p] by the determinant
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $p$ be a prime, and assume $W.\Delta \neq 0$. Write $E = W \otimes \mathbb{Q}$ for the base change of $W$ along the canonical ring homomorphism $\mathbb{Z} \to \mathbb{Q}$, and let $E[p]$ denote the $p$-torsion submodule (`Submodule.torsionBy ℤ … p`) of the group of points of the affine model of $E$ over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, regarded as a module over $\mathbb{Z}/p$. Let $N$ be a $\mathbb{Z}/p$-submodule of $E[p]$ satisfying two hypotheses: cofixedness, namely $\sigma \cdot x - x \in N$ for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ and every $x \in E[p]$; and properness, $N \neq \top$. Then for every such $\sigma$ and every $x \in N$ one has $\sigma \cdot x = \det\bigl(\mathrm{galoisRepModuleEnd}\ \mathbb{Q}\ E\ p\ \sigma\bigr) \cdot x$, where `galoisRepModuleEnd` is the monoid homomorphism sending $\sigma$ to the $\mathbb{Z}/p$-linear endomorphism of $E[p]$ given by the action of $\sigma$, and the determinant is taken as an element of $\mathbb{Z}/p$ acting by scalar multiplication.
--
--   This is the linear-algebra mechanism behind Mazur's reductions: a proper submodule of $E[p]$ on which the Galois action is trivial modulo $N$ (so that the mod-$p$ representation is triangular with trivial quotient character) is acted on through the determinant character. It is used in the Frey-package analysis, by [`FreyPackage.frey_no_cofixed_large`](thm.html#FreyPackage.frey_no_cofixed_large).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_smul_eq_det_smul_of_cofixed.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.smul_eq_det_smul_of_cofixed
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (N : Submodule (ZMod p)
      (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p))
    (hcof : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p),
      σ • x - x ∈ N)
    (htop : N ≠ ⊤)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∀ x ∈ N, σ • x =
      LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p σ) • x := by sorry

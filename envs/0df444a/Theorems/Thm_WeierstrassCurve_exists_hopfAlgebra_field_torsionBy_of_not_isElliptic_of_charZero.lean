-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero
-- name    : WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/11d7dcee-ff11-5022-8dfc-01dc467d0f16
-- title:
--   n-torsion of a non-elliptic Weierstrass curve via a finite Hopf algebra
-- statement:
--   Let $K$ be a field of characteristic zero, let $W$ be a Weierstrass curve over $K$ which is not elliptic (its discriminant fails to be a unit, so over a field $\Delta(W)=0$), and let $n$ be a prime natural number. Then there exist a type $A$ carrying a commutative ring structure and the structure of a $K$-Hopf algebra such that: $A$ is finite as a $K$-module; its comultiplication is cocommutative; and there is a bijection $e_A$ from $\operatorname{Hom}_{K\text{-alg}}(A,\overline K)$, regarded with its convolution monoid structure (`WithConv`), onto the $n$-torsion submodule $\operatorname{torsionBy}_{\mathbb Z}\,n$ of the group of points of the base change of $W$ to an algebraic closure $\overline K$ — that is, the group consisting of the point at infinity together with the nonsingular affine $\overline K$-points — with two further properties: $e_A(f\cdot g)=e_A(f)+e_A(g)$ for all $f,g$, so $e_A$ is an isomorphism of the convolution monoid onto the additive torsion group; and $e_A$ is Galois-equivariant in the sense that for every $\sigma\in\operatorname{Aut}_K(\overline K)$ and all $f,g$ with $g(a)=\sigma(f(a))$ for all $a\in A$, one has $e_A(g)=\sigma\cdot e_A(f)$.
--
--   For a singular Weierstrass curve over a field of characteristic zero the smooth locus is a one-dimensional group of additive or multiplicative type, so its $n$-torsion is finite and is the group of $\overline K$-points of a finite cocommutative $K$-Hopf algebra, equivariantly for the absolute Galois group; the characteristic-zero hypothesis is needed, since in characteristic $p$ the $p$-torsion of the additive group is infinite over an algebraically closed field. It is the degenerate-curve input to the construction of the Galois representation attached to torsion, and is used by the statements specialising the base field to $\mathbb{Q}$ and to $p$-adic fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero
    (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (hW : ¬ W.IsElliptic)
    (n : ℕ) [Fact n.Prime] :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eA : WithConv (A →ₐ[K] AlgebraicClosure K) ≃
            Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f) := by sorry

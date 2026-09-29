-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_rat_torsionBy_withConv_equiv
-- name    : WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/fe33a9c1-2e0b-57cb-b366-278208c87fd1
-- title:
--   E[p] as points of a finite ℚ-Hopf algebra, over ℚ̄ and ℚ̄ₚ
-- statement:
--   Let $E$ be a Weierstrass curve over $\mathbb{Q}$, let $W$ be a Weierstrass curve over $\mathbb{Z}$ which is an integral model of $E$ in the sense that some variable change $C$ over $\mathbb{Q}$ satisfies $C \bullet E = W_{/\mathbb{Q}}$ (the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}$), and let $p$ be a prime. Then there is a type $A$ carrying a commutative ring structure and a Hopf algebra structure over $\mathbb{Q}$ such that: $A$ is finite as a $\mathbb{Q}$-module; its comultiplication is cocommutative; and there are two bijections. First, a bijection $eA$ from the set of $\mathbb{Q}$-algebra homomorphisms $A \to \overline{\mathbb{Q}}$, regarded through `WithConv` as a multiplicative object (convolution), onto the $p$-torsion submodule of the $\mathbb{Z}$-module of affine points of $E$ base changed to $\overline{\mathbb{Q}}$, which sends products to sums and which is Galois equivariant in the following sense: for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and all $f, g$ with $g(a) = \sigma(f(a))$ for all $a \in A$, one has $eA(g) = \sigma \bullet eA(f)$. Second, a bijection $eAp$ with the same two properties, for homomorphisms $A \to \overline{\mathbb{Q}_p}$, onto the $p$-torsion of the points of $W$ base changed along $\mathbb{Z} \to \mathbb{Q}_p$ and then to $\overline{\mathbb{Q}_p}$, equivariant for $\mathrm{Gal}(\overline{\mathbb{Q}_p}/\mathbb{Q}_p)$.
--
--   This packages the $p$-torsion of $E$ as the points of a single finite cocommutative $\mathbb{Q}$-Hopf algebra, i.e. the affine algebra of the finite group scheme $E[p]$ over $\mathbb{Q}$, together with the compatible descriptions of its $\overline{\mathbb{Q}}$- and $\overline{\mathbb{Q}_p}$-points; the $p$-adic side is phrased against the integral model $W$ rather than $E$ itself. It feeds the finite flat prolongation statements used in the analysis of the local behaviour of $E[p]$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_hopfAlgebra_rat_torsionBy_withConv_equiv.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv
    (E : WeierstrassCurve ℚ) {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime] :
    letI : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra ℚ A),
      Module.Finite ℚ A ∧ Coalgebra.IsCocomm ℚ A ∧
      (∃ eA : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) ≃
            Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f)) ∧
      (∃ eAp : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) ≃
            Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point p,
        (∀ f g, eAp (f * g) = eAp f + eAp g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])),
          (∀ a : A, g a = σ (f a)) → eAp g = σ • (eAp f)) := by sorry

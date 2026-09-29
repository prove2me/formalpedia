-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_finiteFree_hopfAlgebra_padicInt_torsionBy_rank_psq_of_isUnit_discr
-- name    : WeierstrassCurve.exists_finiteFree_hopfAlgebra_padicInt_torsionBy_rank_psq_of_isUnit_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/16da4aaa-916c-5d63-adf6-0d093c1604a3
-- title:
--   Finite free rank p² Hopf algebra for W[p], good reduction
-- statement:
--   Let $p$ be a prime and let $W$ be a Weierstrass curve over $\mathbb{Z}_p$ whose discriminant $\Delta(W)$ is a unit of $\mathbb{Z}_p$. Then there exist a type $H$, a commutative ring structure on it and a Hopf algebra structure over $\mathbb{Z}_p$ such that: $H$ is finite and free as a $\mathbb{Z}_p$-module, its comultiplication is cocommutative, $\operatorname{rank}_{\mathbb{Z}_p} H = p^2$, and there is a bijection $eH$ from the convolution monoid $\mathrm{WithConv}\,(H \to_{\mathbb{Z}_p\text{-alg}} \overline{\mathbb{Q}_p})$ of $\mathbb{Z}_p$-algebra homomorphisms from $H$ to an algebraic closure of $\mathbb{Q}_p$ onto the $p$-torsion submodule $\{P : pP = 0\}$ of the group of affine points of $W$ base changed to $\mathbb{Q}_p$ and then to $\overline{\mathbb{Q}_p}$, with the two properties: $eH(f \cdot g) = eH(f) + eH(g)$ for all $f, g$, so that $eH$ carries the convolution product to addition of points; and for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}_p}$ and all $f, g$ with $g(h) = \sigma(f(h))$ for all $h \in H$, one has $eH(g) = \sigma \bullet eH(f)$, the Galois action on points. Thus $eH$ is an isomorphism of Galois groups between the $\overline{\mathbb{Q}_p}$-points of $\operatorname{Spec} H$ and $W[p]$.
--
--   This is the good-reduction case of the statement that the $p$-torsion of an elliptic curve over $\mathbb{Z}_p$ is the group of points of a finite flat group scheme of order $p^2$ over $\mathbb{Z}_p$ (Katz–Mazur, Theorem 2.3.1, in the language of Hopf algebras and points), the input used to exhibit the local flat deformation condition at $p$. It is cited in the construction of a Hopf order inside the Galois-equivariant $p$-torsion over $\mathbb{Q}_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_finiteFree_hopfAlgebra_padicInt_torsionBy_rank_psq_of_isUnit_discr.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine TensorProduct in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_finiteFree_hopfAlgebra_padicInt_torsionBy_rank_psq_of_isUnit_discr
    (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ_[p]) (hΔ : IsUnit W.Δ)
    [DecidableEq (AlgebraicClosure ℚ_[p])] :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Free ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      Module.finrank ℤ_[p] H = p ^ 2 ∧
      ∃ eH : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
            Submodule.torsionBy ℤ ((W⁄ℚ_[p])⁄(AlgebraicClosure ℚ_[p])).Point p,
        (∀ f g, eH (f * g) = eH f + eH g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ h : H, g h = σ (f h)) → eH g = σ • (eH f) := by sorry

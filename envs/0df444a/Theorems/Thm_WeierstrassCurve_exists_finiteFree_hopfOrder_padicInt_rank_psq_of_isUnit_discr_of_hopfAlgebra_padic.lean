-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_finiteFree_hopfOrder_padicInt_rank_psq_of_isUnit_discr_of_hopfAlgebra_padic
-- name    : WeierstrassCurve.exists_finiteFree_hopfOrder_padicInt_rank_psq_of_isUnit_discr_of_hopfAlgebra_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/6630c940-9d4d-5a77-97a7-8d78c384d2b1
-- title:
--   Free ℤₚ-Hopf order of rank p² inside A
-- statement:
--   Let $p$ be a prime and let $W$ be a Weierstrass curve over $\mathbb{Z}_p$ whose discriminant $\Delta(W)$ is a unit of $\mathbb{Z}_p$. Let $A$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Q}_p$, finite as a $\mathbb{Q}_p$-module and with cocommutative comultiplication, and suppose given a bijection $e_A$ from the set of $\mathbb{Q}_p$-algebra homomorphisms $A \to \overline{\mathbb{Q}_p}$, regarded as a monoid under convolution (`WithConv`), onto the $p$-torsion submodule of the group of points of $W$ base changed to $\mathbb{Q}_p$ and then to $\overline{\mathbb{Q}_p}$, such that $e_A(f \cdot g) = e_A(f) + e_A(g)$ for all $f, g$, and such that for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}_p}/\mathbb{Q}_p)$ and all $f, g$ with $g(a) = \sigma(f(a))$ for all $a \in A$ one has $e_A(g) = \sigma \cdot e_A(f)$. Then there exists a commutative ring $H$ with a Hopf algebra structure over $\mathbb{Z}_p$ which is finite and free as a $\mathbb{Z}_p$-module, has cocommutative comultiplication, has $\operatorname{rank}_{\mathbb{Z}_p} H = p^2$, and admits a $\mathbb{Q}_p$-algebra isomorphism $\varphi \colon \mathbb{Q}_p \otimes_{\mathbb{Z}_p} H \to A$ compatible with comultiplication, i.e. $\mathrm{comul}(\varphi(x)) = (\varphi \otimes \varphi)(\mathrm{comul}(x))$ for all $x$.
--
--   This produces the Hopf algebra of the schematic $p$-torsion of an elliptic curve with good reduction over $\mathbb{Z}_p$ as a $\mathbb{Z}_p$-order of rank $p^2$ in the given étale $\mathbb{Q}_p$-Hopf algebra $A$ of $W_{\mathbb{Q}_p}[p]$, the datum $A$ being pinned down only through its points and their Galois action. It feeds the construction of a finite flat prolongation of the $p$-torsion over $\mathbb{Z}_p$, used in the finite-flatness input to the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_finiteFree_hopfOrder_padicInt_rank_psq_of_isUnit_discr_of_hopfAlgebra_padic.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine TensorProduct in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_finiteFree_hopfOrder_padicInt_rank_psq_of_isUnit_discr_of_hopfAlgebra_padic
    (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ_[p]) (hΔ : IsUnit W.Δ)
    [DecidableEq (AlgebraicClosure ℚ_[p])]
    (A : Type) [CommRing A] [HopfAlgebra ℚ_[p] A]
    (hAfin : Module.Finite ℚ_[p] A) (hAcocomm : Coalgebra.IsCocomm ℚ_[p] A)
    (eA : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃
          Submodule.torsionBy ℤ ((W⁄ℚ_[p])⁄(AlgebraicClosure ℚ_[p])).Point p)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Free ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      Module.finrank ℤ_[p] H = p ^ 2 ∧
      ∃ φ : (ℚ_[p] ⊗[ℤ_[p]] H) ≃ₐ[ℚ_[p]] A,
        ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
          (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x) := by sorry

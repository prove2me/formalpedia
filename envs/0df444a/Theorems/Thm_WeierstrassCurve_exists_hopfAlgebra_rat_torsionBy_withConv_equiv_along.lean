-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_rat_torsionBy_withConv_equiv_along
-- name    : WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv_along
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/bbdb11c3-9bd0-5ba1-a5af-9a1c7e5f91aa
-- title:
--   Étale Hopf algebra for E[p] with global and p-adic point identifications
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, equipped with a $\mathbb{Q}$-algebra structure for which $\mathbb{Q}$ is the fraction field of $R$; let $E$ be a Weierstrass curve over $\mathbb{Q}$ and $W_0$ a Weierstrass curve over $R$ whose base change along $R \to \mathbb{Q}$ is $E$; let $p$ be a prime and $f \colon R \to \mathbb{Z}_p$ a ring homomorphism such that for every $r \in R$ the image of $f(r)$ in $\mathbb{Q}_p$ agrees with the image of $r$ under $R \to \mathbb{Q} \to \mathbb{Q}_p$. The conclusion asserts the existence of a commutative ring $A$ carrying a Hopf algebra structure over $\mathbb{Q}$, finite as a $\mathbb{Q}$-module and cocommutative as a coalgebra, together with two bijections. First, a bijection $e_A$ from the $\mathbb{Q}$-algebra homomorphisms $A \to \overline{\mathbb{Q}}$, taken in the type `WithConv` carrying the convolution product, onto the $p$-torsion submodule $\mathrm{torsionBy}_{\mathbb{Z}}$ of the group of points of $E$ over $\overline{\mathbb{Q}}$, which sends convolution products to sums and satisfies: whenever $\sigma \in \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ and $g = \sigma \circ f$ pointwise on $A$, one has $e_A(g) = \sigma \cdot e_A(f)$. Second, a bijection with the same two properties, relative to $\mathrm{Aut}_{\mathbb{Q}_p}(\overline{\mathbb{Q}_p})$, from the $\mathbb{Q}$-algebra homomorphisms $A \to \overline{\mathbb{Q}_p}$ with convolution product onto the $p$-torsion of the points over $\overline{\mathbb{Q}_p}$ of the curve obtained from $W_0$ by pushing forward along $f$ and base changing to $\mathbb{Q}_p$.
--
--   This is the coordinate-ring presentation of the finite étale group scheme $E[p]$ over $\mathbb{Q}$, packaged as a finite cocommutative Hopf $\mathbb{Q}$-algebra whose $\overline{\mathbb{Q}}$- and $\overline{\mathbb{Q}_p}$-points are identified Galois-equivariantly with the $p$-torsion of $E$ and of the $p$-adic model obtained from an abstract integral model $W_0$ along $f$. It is the form of the statement consumed by [`WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_padicInt_along`](thm.html#WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_padicInt_along), where the $p$-adic identification feeds the finite flat prolongation of the $p$-torsion over $\mathbb{Z}_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_hopfAlgebra_rat_torsionBy_withConv_equiv_along.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv_along
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (E : WeierstrassCurve ℚ) (W₀ : WeierstrassCurve R) (heq : W₀⁄ℚ = E)
    (p : ℕ) [Fact p.Prime]
    (f : R →+* ℤ_[p])
    (hfc : ∀ r : R, ((f r : ℤ_[p]) : ℚ_[p]) = (algebraMap ℚ ℚ_[p]) (algebraMap R ℚ r)) :
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
            Submodule.torsionBy ℤ (((W₀.map f)⁄ℚ_[p])⁄(AlgebraicClosure ℚ_[p])).Point p,
        (∀ f g, eAp (f * g) = eAp f + eAp g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])),
          (∀ a : A, g a = σ (f a)) → eAp g = σ • (eAp f)) := by sorry

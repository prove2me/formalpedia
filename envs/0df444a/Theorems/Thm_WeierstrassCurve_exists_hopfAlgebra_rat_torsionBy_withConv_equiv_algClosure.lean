-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_rat_torsionBy_withConv_equiv_algClosure
-- name    : WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv_algClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/74703188-1c73-5e71-a7cb-fca7178b7c49
-- title:
--   E[p] as a finite cocommutative Hopf algebra over ℚ
-- statement:
--   Let $E$ be a Weierstrass curve over $\mathbb{Q}$, given by its five Weierstrass coefficients, and let $p$ be a prime. The assertion is the existence of a type $A$ carrying a commutative ring structure and a Hopf algebra structure over $\mathbb{Q}$ such that: $A$ is finite as a $\mathbb{Q}$-module; its comultiplication is cocommutative; and there is a bijection $e_A$ from `WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)`, that is, the set of $\mathbb{Q}$-algebra homomorphisms from $A$ to an algebraic closure $\overline{\mathbb{Q}}$ equipped with its convolution multiplication coming from the Hopf structure, onto the $p$-torsion submodule $\{P : pP = 0\}$ of the group $(E\otimes\overline{\mathbb{Q}})(\overline{\mathbb{Q}})$ of points of the base-changed Weierstrass curve, viewed as a $\mathbb{Z}$-module. The bijection is required to satisfy two compatibilities: it turns convolution into addition, $e_A(f\cdot g) = e_A(f) + e_A(g)$ for all $f,g$; and it is Galois-equivariant in the form that for every $\sigma \in \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ and all $f, g$ with $g(a) = \sigma(f(a))$ for every $a \in A$, one has $e_A(g) = \sigma \bullet e_A(f)$ for the Galois action on torsion points. No nonsingularity hypothesis is imposed on $E$.
--
--   This provides the affine coordinate ring of the finite $\mathbb{Q}$-group scheme $E[p] = \ker([p])$, together with the identification of its $\overline{\mathbb{Q}}$-points with $E[p](\overline{\mathbb{Q}})$ as a Galois module; it is the Hopf-algebraic input to the construction of the mod $p$ representation attached to $E$. It is used by [`WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv`](thm.html#WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_hopfAlgebra_rat_torsionBy_withConv_equiv_algClosure.lean

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

theorem WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv_algClosure
    (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] :
    letI : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra ℚ A),
      Module.Finite ℚ A ∧ Coalgebra.IsCocomm ℚ A ∧
      ∃ eA : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) ≃
            Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f) := by sorry

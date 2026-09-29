-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_ratLocalizedAt_of_padicInt
-- name    : WeierstrassCurve.exists_finiteFlat_prolongation_torsion_ratLocalizedAt_of_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/efaf3f1b-7f07-59cc-a3a3-89e4235bbdc1
-- title:
--   Descent of a finite flat prolongation of E[p] to ℤ₍ₚ₎
-- statement:
--   Let $E$ be a Weierstrass curve over $\mathbb{Q}$ and $W$ a Weierstrass curve over $\mathbb{Z}$ which is an integral model of $E$, in the sense that some variable change over $\mathbb{Q}$ carries $E$ to the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}$, and let $p$ be a prime. The hypothesis is a local prolongation datum: there exist a type $H$ with a commutative ring structure and a Hopf algebra structure over $\mathbb{Z}_p$ such that $H$ is finite and flat as a $\mathbb{Z}_p$-module and its comultiplication is cocommutative, together with an equivalence $e$ between `WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])`, the multiplicative avatar of the set of $\mathbb{Z}_p$-algebra homomorphisms from $H$ to an algebraic closure of $\mathbb{Q}_p$, and the $p$-torsion subgroup `Submodule.torsionBy ℤ … p` of the group of points of the base change of $W$ to that algebraic closure, such that $e$ sends the multiplication to addition of points and is Galois-equivariant in the sense that whenever $g$ is the pointwise composite of $f$ with $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}_p}/\mathbb{Q}_p)$ one has $e(g) = \sigma \cdot e(f)$. The conclusion asserts the same package over the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$, i.e. $\mathbb{Z}_{(p)}$: there are a commutative ring $H$ with a Hopf algebra structure over that subring, finite and flat as a module over it and cocommutative, and an equivalence between `WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)` and the $p$-torsion of the points of $E$ over an algebraic closure of $\mathbb{Q}$, additive for the multiplication and equivariant for $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ in the same sense.
--
--   In the language of affine Hopf algebras this says that a finite flat prolongation over $\mathbb{Z}_p$ of the $p$-torsion of $E$, as a Galois module, descends along $\mathbb{Z}_{(p)} \hookrightarrow \mathbb{Z}_p$ to a finite flat prolongation of $E[p]$ over $\mathbb{Z}_{(p)}$. It feeds the global finite-flatness input used in [`WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_tateParameter_of_peuRamifiee`](thm.html#WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_tateParameter_of_peuRamifiee), where the local hypothesis is supplied by a Tate-parameter (peu ramifiée) analysis at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_ratLocalizedAt_of_padicInt.lean

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

theorem WeierstrassCurve.exists_finiteFlat_prolongation_torsion_ratLocalizedAt_of_padicInt
    (E : WeierstrassCurve ℚ) {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime]
    (hloc : letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
      ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
        Module.Finite ℤ_[p] H ∧
        Module.Flat ℤ_[p] H ∧
        Coalgebra.IsCocomm ℤ_[p] H ∧
        ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
            Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point p,
          (∀ f g, e (f * g) = e f + e g) ∧
          ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
            (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
            (∀ h : H, g h = σ (f h)) → e g = σ • (e f)) :
    letI : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by sorry

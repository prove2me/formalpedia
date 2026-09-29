-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_isUnit_discr
-- name    : WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_isUnit_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/a1d6c1e5-c735-5c3a-ab0c-2590e7c365d7
-- title:
--   Finite flat ℤₚ-prolongation of p-torsion in good reduction
-- statement:
--   Let $p$ be a prime and let $W$ be a Weierstrass curve over $\mathbb{Z}_p$ whose discriminant $\Delta(W)$ is a unit of $\mathbb{Z}_p$. The assertion is the existence of a type $H$ carrying a commutative ring structure and the structure of a Hopf algebra over $\mathbb{Z}_p$, such that $H$ is finite and flat as a $\mathbb{Z}_p$-module, its coalgebra structure is cocommutative, and there is a bijection $e$ from the set of $\mathbb{Z}_p$-algebra homomorphisms $H \to \overline{\mathbb{Q}_p}$, equipped with its convolution monoid structure (the type `WithConv`), onto the submodule of elements killed by $p$ of the group of points of $W$ base changed first to $\mathbb{Q}_p$ and then to $\overline{\mathbb{Q}_p} =$ `AlgebraicClosure ℚ_[p]`, with two properties: $e$ carries convolution to addition, $e(f\cdot g) = e(f) + e(g)$; and $e$ is Galois equivariant in the sense that for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}_p}$ and all $f, g$ with $g(h) = \sigma(f(h))$ for all $h \in H$, one has $e(g) = \sigma \cdot e(f)$. Thus the $p$-torsion of $W_{\mathbb{Q}_p}$ over $\overline{\mathbb{Q}_p}$, as a module over the local Galois group, is realised by the $\overline{\mathbb{Q}_p}$-points of a finite flat commutative group scheme over $\mathbb{Z}_p$.
--
--   This is the good-reduction case of the prolongation statement for $p$-torsion at level $n = 1$: a Weierstrass model over $\mathbb{Z}_p$ with unit discriminant is an elliptic curve over $\mathbb{Z}_p$, and its $p$-torsion subscheme provides the finite flat prolongation of the Galois module $W_{\mathbb{Q}_p}[p](\overline{\mathbb{Q}_p})$. It feeds the statement [`WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_integralModel_isUnit_discr`](thm.html#WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_integralModel_isUnit_discr), and through it the finite-flatness input to the local conditions imposed on deformations at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_isUnit_discr.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_isUnit_discr
    (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ_[p]) (hΔ : IsUnit W.Δ) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
          Submodule.torsionBy ℤ ((W⁄ℚ_[p])⁄(AlgebraicClosure ℚ_[p])).Point p,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by sorry

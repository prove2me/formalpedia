-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv
-- name    : WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/fed8daf3-55a1-53f3-a952-099f4d03f46a
-- title:
--   Sign twist preserves finite flat prolongation of p-torsion
-- statement:
--   Let $p$ be a prime, let $E_1,E_2$ be Weierstrass curves over $\mathbb{Q}_p$, let $d\in\mathbb{Q}_p$ have $\|d\|=1$, and let $s$ in $\overline{\mathbb{Q}_p}=\mathrm{AlgebraicClosure}\,\mathbb{Q}_p$ satisfy $s^2=d$. Write $E_i[p]$ for the $\mathbb{Z}$-submodule $\mathrm{Submodule.torsionBy}\ \mathbb{Z}\ (E_i/\overline{\mathbb{Q}_p}).\mathrm{Point}\ p$ of points of the base-changed curve killed by $p$. Assume given an additive isomorphism $\varphi\colon E_1[p]\to E_2[p]$ which for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}_p}$ satisfies $\varphi(\sigma\cdot P)=\sigma\cdot\varphi(P)$ for all $P$ when $\sigma s=s$, and $\varphi(\sigma\cdot P)=-(\sigma\cdot\varphi(P))$ for all $P$ when $\sigma s\neq s$. Assume further that $E_2[p]$ admits a prolongation datum: a type $H$ carrying a commutative ring structure and a $\mathbb{Z}_p$-Hopf algebra structure, finite and flat as a $\mathbb{Z}_p$-module and with cocommutative comultiplication, together with a bijection $e$ from the set of $\mathbb{Z}_p$-algebra maps $H\to\overline{\mathbb{Q}_p}$ equipped with its convolution product (`WithConv`) onto $E_2[p]$, such that $e(f*g)=e(f)+e(g)$ and such that whenever $g(h)=\sigma(f(h))$ for all $h\in H$ one has $e(g)=\sigma\cdot e(f)$. The conclusion is that $E_1[p]$ admits a prolongation datum of exactly the same shape: some $H$ as above with a Galois-compatible, convolution-to-addition bijection onto $E_1[p]$.
--
--   This is the transport step saying that twisting by the quadratic character attached to a unit $d\in\mathbb{Z}_p^\times$ does not destroy the existence of a finite flat commutative prolongation of the $p$-torsion over $\mathbb{Z}_p$, stated in the Hopf-algebra currency used throughout for such prolongations. It is used in the Tate-curve branch of the local analysis at $p$, where the $p$-torsion of one curve is identified with a sign twist of that of another.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv
    (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure ℚ_[p])]
    (E₁ E₂ : WeierstrassCurve ℚ_[p])
    (d : ℚ_[p]) (hd : ‖d‖₊ = 1)
    (s : AlgebraicClosure ℚ_[p]) (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d)
    (φ : Submodule.torsionBy ℤ (E₁⁄(AlgebraicClosure ℚ_[p])).Point p
          ≃+ Submodule.torsionBy ℤ (E₂⁄(AlgebraicClosure ℚ_[p])).Point p)
    (hφ : ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
        (σ s = s → ∀ P, φ (σ • P) = σ • φ P) ∧
        (σ s ≠ s → ∀ P, φ (σ • P) = -(σ • φ P)))
    (hE₂ : ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
        Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
        ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
            Submodule.torsionBy ℤ (E₂⁄(AlgebraicClosure ℚ_[p])).Point p,
          (∀ f g, e (f * g) = e f + e g) ∧
          ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
            (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
            (∀ h : H, g h = σ (f h)) → e g = σ • (e f)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
          Submodule.torsionBy ℤ (E₁⁄(AlgebraicClosure ℚ_[p])).Point p,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by sorry

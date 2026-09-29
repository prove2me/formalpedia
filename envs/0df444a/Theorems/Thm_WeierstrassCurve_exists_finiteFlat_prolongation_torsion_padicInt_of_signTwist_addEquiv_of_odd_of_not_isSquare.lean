-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv_of_odd_of_not_isSquare
-- name    : WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv_of_odd_of_not_isSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/9437b7e6-a74a-5421-a132-af7c5d925948
-- title:
--   Sign twist by an unramified quadratic character preserves finite flat models
-- statement:
--   Let $p$ be a prime with $p \neq 2$ (with decidable equality on $\overline{\mathbb{Q}}_p$ assumed for definiteness), let $E_1, E_2$ be Weierstrass curves over $\mathbb{Q}_p$, let $d \in \mathbb{Q}_p$ satisfy $\|d\|=1$ and not be a square, and let $s \in \overline{\mathbb{Q}}_p$ satisfy $s^2 = d$. Suppose given an additive isomorphism $\varphi$ between the $p$-torsion subgroups (the $\mathbb{Z}$-submodules killed by $p$) of the groups of points of $E_1$ and of $E_2$ over $\overline{\mathbb{Q}}_p$, which is a sign twist: for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$, if $\sigma s = s$ then $\varphi(\sigma \cdot P) = \sigma \cdot \varphi(P)$ for all $P$, and if $\sigma s \neq s$ then $\varphi(\sigma \cdot P) = -(\sigma \cdot \varphi(P))$ for all $P$. Assume $E_2[p]$ admits a finite flat model: a commutative ring $H$ which is a $\mathbb{Z}_p$-Hopf algebra, finite and flat as a $\mathbb{Z}_p$-module and cocommutative, together with a bijection $e$ from the convolution monoid $\mathrm{WithConv}$ on $\mathrm{Hom}_{\mathbb{Z}_p\text{-alg}}(H, \overline{\mathbb{Q}}_p)$ onto $E_2[p]$ carrying convolution to addition and carrying postcomposition by $\sigma$ to the Galois action. Then $E_1[p]$ admits such a model as well.
--
--   This is the descent step showing that a finite flat group-scheme model over $\mathbb{Z}_p$ for the $p$-torsion of one curve transports to a curve whose $p$-torsion differs by a sign twist, in the case where the twisting quadratic extension $\mathbb{Q}_p(\sqrt d)$ is unramified; it feeds the argument that Frey-curve torsion representations are finite flat at $p$, and is used by [`WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv`](thm.html#WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv), where the remaining (easy) cases $p = 2$ and $d$ a square are handled separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv_of_odd_of_not_isSquare.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_finiteFlat_prolongation_torsion_padicInt_of_signTwist_addEquiv_of_odd_of_not_isSquare
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [DecidableEq (AlgebraicClosure ℚ_[p])]
    (E₁ E₂ : WeierstrassCurve ℚ_[p])
    (d : ℚ_[p]) (hd : ‖d‖₊ = 1) (hd_nsq : ¬ IsSquare d)
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

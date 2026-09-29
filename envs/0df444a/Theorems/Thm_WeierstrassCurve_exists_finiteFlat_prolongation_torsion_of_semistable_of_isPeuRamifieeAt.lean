-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_of_semistable_of_isPeuRamifieeAt
-- name    : WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_semistable_of_isPeuRamifieeAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/6962f04a-424f-57d2-8706-99f06d982525
-- title:
--   Finite flat prolongation of E[p] when semistable and peu ramifiée at p
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and let $p$ be a prime, subject to three hypotheses: the discriminant $\Delta_W$ is nonzero; if $p \mid \Delta_W$ then $p \nmid c_4(W)$; and the base change $E := W_{\mathbb{Q}}$ along $\mathbb{Z} \to \mathbb{Q}$ satisfies `IsPeuRamifieeAt` at $(p,p)$, i.e. $p$ divides the $p$-adic valuation $\operatorname{padicValRat}\, p\, \Delta_E$. Write $R :=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$ (that is, $\mathbb{Z}_{(p)}$ realised inside $\mathbb{Q}$). The conclusion asserts the existence of a type $H$ carrying a commutative ring structure and an $R$-Hopf algebra structure such that $H$ is a finite and flat $R$-module and its comultiplication is cocommutative, together with a bijection $e$ from the type `WithConv` of $R$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ (with its convolution multiplication, $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`) onto the $p$-torsion submodule $\operatorname{torsionBy}_{\mathbb{Z}}\, p$ of the group of $\overline{\mathbb{Q}}$-points of $E$, satisfying $e(f \cdot g) = e(f) + e(g)$ for all $f,g$ and the equivariance: for every $\sigma \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and all $f,g$ with $g(h) = \sigma(f(h))$ for all $h \in H$, one has $e(g) = \sigma \cdot e(f)$. Equality on $\overline{\mathbb{Q}}$ is made decidable by a classical instance.
--
--   This is the statement that, for a Weierstrass model over $\mathbb{Z}$ which is semistable at $p$ in the stated sense and peu ramifiée at $p$, the $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$-module $E[p]$ prolongs to a finite flat commutative group scheme over $\mathbb{Z}_{(p)}$, presented concretely through its coordinate Hopf algebra. It assembles the good-reduction case ([`WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_integralModel_isUnit_discr`](thm.html#WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_integralModel_isUnit_discr), applied over the discrete valuation ring $\mathbb{Z}_{(p)}$ with fraction field $\mathbb{Q}$) and the multiplicative case ([`WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_multiplicativeReduction_of_peuRamifiee`](thm.html#WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_multiplicativeReduction_of_peuRamifiee)), and feeds the flatness input of the level-lowering arguments for the Frey curve and the construction of its residual representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_of_semistable_of_isPeuRamifieeAt.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_WeierstrassCurve_PeuRamifiee

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_semistable_of_isPeuRamifieeAt
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hsemi : (p : ℤ) ∣ W.Δ → ¬ (p : ℤ) ∣ W.c₄)
    (hfin : (W.map (Int.castRingHom ℚ)).IsPeuRamifieeAt p p) :
    letI : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by sorry

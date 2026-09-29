-- Prove2me | Theorems.Thm_WeierstrassProjModel_projModelCR_sections_twoChart
-- name    : WeierstrassProjModel.projModelCR_sections_twoChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/b2a541d4-3fae-5e20-a61b-16113a3ffde6
-- title:
--   Two-chart description of global sections of the Weierstrass model
-- statement:
--   Let $R$ be a commutative ring and $V$ a projective Weierstrass cubic over $R$. Put $A = R[X_0,X_1,X_2]/(V.\mathrm{polynomial})$ and let $\mathcal A =$ `projModelGradingCR V` be its grading, $\mathcal A_i$ being the image of the degree-$i$ homogeneous submodule of $R[X_0,X_1,X_2]$ under the quotient map; write $Y$, $Z$ for the classes of $X_1$, $X_2$, which lie in $\mathcal A_1$. Let $\rho_Y$ and $\rho_Z$ be the ring maps from $\Gamma(\mathrm{Proj}\,\mathcal A, \top)$ to the degree-zero homogeneous localisations $\mathrm{Away}\,\mathcal A\,Y$ and $\mathrm{Away}\,\mathcal A\,Z$ obtained by restricting a global section to the basic open set and inverting Mathlib's identification `Proj.basicOpenIsoAway` of that section ring with the localisation. The assertion is fourfold: $\rho_Y$ and $\rho_Z$ are jointly injective; any pair $(a,b)$ with equal images in $\mathrm{Away}\,\mathcal A\,(YZ)$ under the two canonical maps `awayMap` comes from a global section $s$ with $\rho_Y s = a$, $\rho_Z s = b$; for every global section $s$ these two images of $\rho_Y s$ and $\rho_Z s$ agree; and for $r \in \mathcal A_0$ the pullback of $r$ along the structure morphism $\mathrm{Proj}\,\mathcal A \to \mathrm{Spec}\,\mathcal A_0$ is sent by $\rho_Y$ and by $\rho_Z$ to $r/1$.
--
--   This is the sheaf axiom for the two-element cover of $\mathrm{Proj}$ of the homogeneous coordinate ring of a Weierstrass cubic by the charts $D_+(Y)$ and $D_+(Z)$, stated as an equaliser description of the ring of global sections together with the normalisation of constants coming from $\mathcal A_0$. It feeds the computation of global sections after base change, [`WeierstrassProjModel.bijective_appTop_pullback_snd_projModelStrCR`](thm.html#WeierstrassProjModel.bijective_appTop_pullback_snd_projModelStrCR).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_projModelCR_sections_twoChart.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  HomogeneousLocalization HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.projModelCR_sections_twoChart
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) :
    let 𝒜 := projModelGradingCR V
    let Y : ProjModelRingCR V := Ideal.Quotient.mk _ (MvPolynomial.X 1)
    let Z : ProjModelRingCR V := Ideal.Quotient.mk _ (MvPolynomial.X 2)
    let hY : Y ∈ 𝒜 1 :=
      mk_mem_quotGradingSubmodule _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 1))
    let hZ : Z ∈ 𝒜 1 :=
      mk_mem_quotGradingSubmodule _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 2))
    let ρY : Γ(Proj 𝒜, ⊤) ⟶ CommRingCat.of (Away 𝒜 Y) :=
      (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫ (Proj.basicOpenIsoAway 𝒜 Y hY one_pos).inv
    let ρZ : Γ(Proj 𝒜, ⊤) ⟶ CommRingCat.of (Away 𝒜 Z) :=
      (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫ (Proj.basicOpenIsoAway 𝒜 Z hZ one_pos).inv
    (∀ s t : Γ(Proj 𝒜, ⊤), ρY s = ρY t → ρZ s = ρZ t → s = t) ∧
    (∀ (a : Away 𝒜 Y) (b : Away 𝒜 Z),
      awayMap 𝒜 hZ (rfl : Y * Z = Y * Z) a = awayMap 𝒜 hY (mul_comm Y Z) b →
      ∃ s : Γ(Proj 𝒜, ⊤), ρY s = a ∧ ρZ s = b) ∧
    (∀ s : Γ(Proj 𝒜, ⊤), awayMap 𝒜 hZ (rfl : Y * Z = Y * Z) (ρY s) = awayMap 𝒜 hY (mul_comm Y Z) (ρZ s)) ∧
    (∀ r : 𝒜 0,
      ρY ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv r)) =
        fromZeroRingHom 𝒜 (Submonoid.powers Y) r ∧
      ρZ ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv r)) =
        fromZeroRingHom 𝒜 (Submonoid.powers Z) r) := by sorry

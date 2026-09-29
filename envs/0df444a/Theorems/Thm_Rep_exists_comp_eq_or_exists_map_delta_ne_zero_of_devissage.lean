-- Prove2me | Theorems.Thm_Rep_exists_comp_eq_or_exists_map_delta_ne_zero_of_devissage
-- name    : Rep.exists_comp_eq_or_exists_map_delta_ne_zero_of_devissage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/63d5c0c1-4bba-5a6c-ad4a-4f82f0089483
-- title:
--   Dévissage four-lemma for the degree-one duality dichotomy
-- statement:
--   Let $G$ be a finite group and $C$ an object of `Rep ℤ G`, i.e. a $\mathbb{Z}[G]$-module, let $p$ be a prime, and let $SB$ be a short complex $SB.X_1 \to SB.X_2 \to SB.X_3$ of $\mathbb{Z}[G]$-modules which is short exact, with every element of $SB.X_3$ killed by $p$. Assume given three short exact presentations, i.e. morphisms $f_B : R_B \to P_B$, $g_B : P_B \to SB.X_1$ with $f_B \circ g_B = 0$ whose short complex is short exact, and likewise $f_I : R_I \to P_I$, $g_I : P_I \to SB.X_2$ and $f_1 : R_1 \to P_1$, $g_1 : P_1 \to SB.X_3$; assume also comparison morphisms $\iota_R : R_B \to R_I$, $\iota_P : P_B \to P_I$ making the two evident squares with $f_B, f_I$ and with $g_B, SB.f, g_I$ commute, and $\rho_R : R_I \to R_1$, $\rho_P : P_I \to P_1$ making the corresponding squares with $f_I, f_1$ and with $g_I, SB.g, g_1$ commute. For a morphism $\varphi$ out of $R_B$ write $\alpha(\varphi)(y) = \varphi_*(\delta y)$, where $\delta$ is the connecting map $H^1(G, SB.X_1) \to H^2(G, R_B)$ of the presentation of $SB.X_1$ and $\varphi_*$ is the induced map on $H^2$ along the identity of $G$; analogously for $R_I$ and $R_1$. The hypotheses are: (1) every $\varphi : R_B \to C$ with $\alpha(\varphi) = 0$ can be written $\varphi = \iota_R \circ \psi + f_B \circ \chi$ for some $\psi : R_I \to C$, $\chi : P_B \to C$; (2) every $\psi : R_I \to C$ either factors as $f_I \circ \chi$ for some $\chi : P_I \to C$, or satisfies $\alpha(\psi)(y) \neq 0$ for some $y \in H^1(G, SB.X_2)$; (3) every additive map $\theta : H^1(G, SB.X_3) \to H^2(G, C)$ is of the form $\alpha(\vartheta)$ for some $\vartheta : R_1 \to C$. The conclusion is that for every $\varphi : R_B \to C$, either $\varphi = f_B \circ \chi$ for some $\chi : P_B \to C$, or $\varphi_*(\delta y) \neq 0$ in $H^2(G, C)$ for some $y \in H^1(G, SB.X_1)$.
--
--   This is the dévissage (four-lemma) assembly step which transfers the dichotomy "a homomorphism on the relation module extends to the presenting module, or else it is detected in degree two by the connecting map" from a submodule–quotient pair to the submodule itself, in the pattern of Milne's proof that the duality maps $\alpha^r$ are controlled by the case of $\mathbb{Z}/m$. It is used in the Herbrand-type step [`M4aHerbrand.exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero`](thm.html#M4aHerbrand.exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero), where the modules in question are built from $S$-idèle class groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_comp_eq_or_exists_map_delta_ne_zero_of_devissage.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_comp_eq_or_exists_map_delta_ne_zero_of_devissage
    {G : Type} [Group G] [Fintype G] (C : Rep ℤ G)
    (p : ℕ) [Fact p.Prime]
    {SB : ShortComplex (Rep ℤ G)} (hSB : SB.ShortExact) (hB₁ : ∀ b : SB.X₃, p • b = 0)

    {R_B P_B : Rep ℤ G} (f_B : R_B ⟶ P_B) (g_B : P_B ⟶ SB.X₁) (w_B : f_B ≫ g_B = 0)
    (hT_B : (ShortComplex.mk f_B g_B w_B).ShortExact)
    {R_I P_I : Rep ℤ G} (f_I : R_I ⟶ P_I) (g_I : P_I ⟶ SB.X₂) (w_I : f_I ≫ g_I = 0)
    (hT_I : (ShortComplex.mk f_I g_I w_I).ShortExact)
    {R₁ P₁ : Rep ℤ G} (f₁ : R₁ ⟶ P₁) (g₁ : P₁ ⟶ SB.X₃) (w₁ : f₁ ≫ g₁ = 0)
    (hT₁ : (ShortComplex.mk f₁ g₁ w₁).ShortExact)

    (ιR : R_B ⟶ R_I) (ιP : P_B ⟶ P_I) (sq₁ : f_B ≫ ιP = ιR ≫ f_I) (sq₂ : g_B ≫ SB.f = ιP ≫ g_I)
    (ρR : R_I ⟶ R₁) (ρP : P_I ⟶ P₁) (sq₃ : f_I ≫ ρP = ρR ≫ f₁) (sq₄ : g_I ≫ SB.g = ρP ≫ g₁)

    (hker : ∀ φ : R_B ⟶ C,
      (∀ y : groupCohomology SB.X₁ 1,
        (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hT_B 1 2 rfl).hom y) = 0) →
      ∃ (ψ : R_I ⟶ C) (χ : P_B ⟶ C), φ = ιR ≫ ψ + f_B ≫ χ)

    (hmid : ∀ ψ : R_I ⟶ C,
      (∃ χ : P_I ⟶ C, ψ = f_I ≫ χ) ∨
      (∃ y : groupCohomology SB.X₂ 1,
        (groupCohomology.map (MonoidHom.id G) ψ 2).hom ((groupCohomology.δ hT_I 1 2 rfl).hom y) ≠ 0))

    (hsurj : ∀ θ : groupCohomology SB.X₃ 1 →+ groupCohomology C 2,
      ∃ ϑ : R₁ ⟶ C, ∀ y : groupCohomology SB.X₃ 1,
        (groupCohomology.map (MonoidHom.id G) ϑ 2).hom ((groupCohomology.δ hT₁ 1 2 rfl).hom y) = θ y)
    (φ : R_B ⟶ C) :
    (∃ χ : P_B ⟶ C, φ = f_B ≫ χ) ∨
    (∃ y : groupCohomology SB.X₁ 1,
      (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hT_B 1 2 rfl).hom y) ≠ 0) := by sorry

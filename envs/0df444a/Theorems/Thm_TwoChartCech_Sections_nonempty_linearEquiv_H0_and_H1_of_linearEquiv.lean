-- Prove2me | Theorems.Thm_TwoChartCech_Sections_nonempty_linearEquiv_H0_and_H1_of_linearEquiv
-- name    : TwoChartCech.Sections.nonempty_linearEquiv_H0_and_H1_of_linearEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/46c042f1-acbe-51e9-bdb7-8717e228aca5
-- title:
--   Transport of two-chart Čech H⁰ and H¹ along equivalences
-- statement:
--   Let $R$ be a commutative ring and let $\mathcal{U}$, $\mathcal{U}'$ be two-chart covers over $R$, i.e. data consisting of three commutative $R$-algebras $A_0, A_1, A_{01}$ together with $R$-algebra maps $\rho_0 : A_0 \to A_{01}$, $\rho_1 : A_1 \to A_{01}$ (the two covers may live in different universes). Let $S$ be sections data for $\mathcal{U}$ and $S'$ sections data for $\mathcal{U}'$: modules $M_0$ over $A_0$, $M_1$ over $A_1$, $M_{01}$ over $A_{01}$, each also an $R$-module compatibly with the algebra structure, together with $R$-linear restrictions $r_0 : M_0 \to M_{01}$, $r_1 : M_1 \to M_{01}$ that are semilinear along $\rho_0$, $\rho_1$ respectively; write $M_0', M_1', M_{01}', r_0', r_1'$ for the corresponding data of $S'$. Assume given $R$-linear equivalences $e_0 : M_0 \simeq M_0'$, $e_1 : M_1 \simeq M_1'$, $e_{01} : M_{01} \simeq M_{01}'$ satisfying $e_{01}(r_0 m) = r_0'(e_0 m)$ for all $m \in M_0$ and $e_{01}(r_1 m) = r_1'(e_1 m)$ for all $m \in M_1$; no compatibility with the chart rings or with $\rho_0, \rho_1$ is required of $e_0, e_1, e_{01}$. The conclusion asserts: the $R$-modules $H^0(S)$ and $H^0(S')$ are linearly isomorphic, and so are $H^1(S)$ and $H^1(S')$, where $H^0$ is the kernel of the Čech differential $M_0 \times M_1 \to M_{01}$ given by the difference of the two restrictions and $H^1$ is the quotient of $M_{01}$ by its range (the two existence claims are stated as `Nonempty` of the types of linear equivalences); moreover $\operatorname{finrank}_R H^0(S) = \operatorname{finrank}_R H^0(S')$ and $H^1(S)$ is subsingleton if and only if $H^1(S')$ is.
--
--   This is the functoriality of the Čech complex of a two-chart cover in its coefficient data, in the form needed to transport the two Čech invariants of one sections datum to another. It is used to compare the cohomology of a line bundle on a two-affine cover of a glued curve with that of an explicit algebraic model, and is cited in the computations of Euler characteristics for two glued curves and in the relative Picard group arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_Sections_nonempty_linearEquiv_H0_and_H1_of_linearEquiv.lean

import Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v v' w w'

open TwoChartCech

theorem TwoChartCech.Sections.nonempty_linearEquiv_H0_and_H1_of_linearEquiv
    {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} {𝒰' : Cover.{u, v'} R}
    (S : Sections.{u, v, w} 𝒰) (S' : Sections.{u, v', w'} 𝒰')
    (e₀ : S.M0 ≃ₗ[R] S'.M0) (e₁ : S.M1 ≃ₗ[R] S'.M1) (e₀₁ : S.M01 ≃ₗ[R] S'.M01)
    (h₀ : ∀ m : S.M0, e₀₁ (S.r0 m) = S'.r0 (e₀ m)) (h₁ : ∀ m : S.M1, e₀₁ (S.r1 m) = S'.r1 (e₁ m)) :
    (Nonempty (↥S.H0 ≃ₗ[R] ↥S'.H0) ∧ Nonempty (S.H1 ≃ₗ[R] S'.H1)) ∧
      Module.finrank R ↥S.H0 = Module.finrank R ↥S'.H0 ∧ (Subsingleton S.H1 ↔ Subsingleton S'.H1) := by sorry

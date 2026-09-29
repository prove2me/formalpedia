-- Prove2me | Theorems.Thm_TwoChartCech_exists_linearEquiv_gluedLinesSections_of_invertible
-- name    : TwoChartCech.exists_linearEquiv_gluedLinesSections_of_invertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/43a61db8-e77e-5d4b-879a-28cdb210c627
-- title:
--   Invertible sections on glued lines are the model ones
-- statement:
--   Let $k$ be a field, $s \in \mathbb{N}$, and let $a, b : \mathrm{Fin}\,s \to k^\times$ be injective families. Let $\mathcal U$ be a two-chart cover over $k$, i.e. $k$-algebras $A_0, A_1, A_{01}$ with $k$-algebra maps $\rho_0 : A_0 \to A_{01}$, $\rho_1 : A_1 \to A_{01}$, and let $S$ be sections data on $\mathcal U$: modules $M_0, M_1, M_{01}$ over $A_0, A_1, A_{01}$ respectively, each also a $k$-module compatibly, together with $k$-linear $r_0 : M_0 \to M_{01}$, $r_1 : M_1 \to M_{01}$ satisfying $r_j(x \cdot t) = \rho_j(x) \cdot r_j(t)$. Assume $k$-algebra isomorphisms $\varphi_0, \varphi_1, \varphi_{01}$ from $A_0, A_1, A_{01}$ onto the chart algebras of `gluedLinesCover k a b` — namely the pairs of Laurent polynomials $(f,g)$ with $f(a_i) = g(b_i)$ for all $i$, both entries having non-negative (resp. non-positive) exponent support for the first (resp. second) chart, and with no support condition for the overlap, the restrictions being the inclusions — with $\varphi_{01} \circ \rho_j = \rho_j' \circ \varphi_j$ for $j = 0,1$. Assume $M_0$ is an invertible $A_0$-module and $M_1$ an invertible $A_1$-module. Regard $A_{01}$ as an $A_0$- and as an $A_1$-algebra via $\rho_0$, $\rho_1$. Then for all $A_{01}$-linear isomorphisms $A_{01} \otimes_{A_0} M_0 \xrightarrow{\sim} M_{01}$ and $A_{01} \otimes_{A_1} M_1 \xrightarrow{\sim} M_{01}$ carrying $1 \otimes t$ to $r_0(t)$, resp. $r_1(t)$, there exist $n, m \in \mathbb{Z}$, a family $\lambda : \mathrm{Fin}\,s \to k^\times$, and $k$-linear (not $A_\bullet$-linear) isomorphisms $e_0, e_1, e_{01}$ from $M_0, M_1, M_{01}$ onto the three modules of `gluedLinesSections k a b lam n m` — the pairs of Laurent polynomials satisfying the condition `GluedCond a b lam`, intersected with the polynomial pairs for the $M_0$-part and with the condition that $f \cdot T^{-n}$ and $g \cdot T^{-m}$ have non-positive support for the $M_1$-part, the model restrictions being the inclusions — such that $e_{01} \circ r_0 = r_0' \circ e_0$ and $e_{01} \circ r_1 = r_1' \circ e_1$.
--
--   This is the Milnor-patching classification in the case at hand: any abstract invertible sections datum on a two-chart cover isomorphic to the standard cover of two lines glued at the $s$ pairs of points $(a_i, b_i)$ is, as a diagram of $k$-vector spaces with restrictions, the explicit model datum of bidegree $(n,m)$ with gluing multipliers $\lambda$. It is used by the comparison of sections and Euler characteristics for pullbacks in the two-glued-projective-lines setting, where the chart isomorphisms come from the structure-sheaf dictionary and the base-change isomorphisms from invertibility of the line bundle on each chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_exists_linearEquiv_gluedLinesSections_of_invertible.lean

import Mathlib
import Definitions.Def_TwoChartCech_GluedLines

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TwoChartCech TensorProduct

universe u

theorem TwoChartCech.exists_linearEquiv_gluedLinesSections_of_invertible
    (k : Type u) [Field k] {s : ℕ} (a b : Fin s → kˣ) (ha : Function.Injective a) (hb : Function.Injective b)
    (𝒰 : Cover.{u, u} k) (S : Sections.{u, u, u} 𝒰)
    (φ₀ : 𝒰.A0 ≃ₐ[k] (gluedLinesCover k a b).A0) (φ₁ : 𝒰.A1 ≃ₐ[k] (gluedLinesCover k a b).A1)
    (φ₀₁ : 𝒰.A01 ≃ₐ[k] (gluedLinesCover k a b).A01)
    (hφ₀ : ∀ f, φ₀₁ (𝒰.ρ0 f) = (gluedLinesCover k a b).ρ0 (φ₀ f))
    (hφ₁ : ∀ f, φ₀₁ (𝒰.ρ1 f) = (gluedLinesCover k a b).ρ1 (φ₁ f))
    [Module.Invertible 𝒰.A0 S.M0] [Module.Invertible 𝒰.A1 S.M1] :
    letI : Algebra 𝒰.A0 𝒰.A01 := 𝒰.ρ0.toRingHom.toAlgebra
    letI : Algebra 𝒰.A1 𝒰.A01 := 𝒰.ρ1.toRingHom.toAlgebra
    ∀ (rbc0 : 𝒰.A01 ⊗[𝒰.A0] S.M0 ≃ₗ[𝒰.A01] S.M01) (rbc1 : 𝒰.A01 ⊗[𝒰.A1] S.M1 ≃ₗ[𝒰.A01] S.M01),
      (∀ t, rbc0 ((1 : 𝒰.A01) ⊗ₜ[𝒰.A0] t) = S.r0 t) →
      (∀ t, rbc1 ((1 : 𝒰.A01) ⊗ₜ[𝒰.A1] t) = S.r1 t) →
      ∃ (n m : ℤ) (lam : Fin s → kˣ)
        (e₀ : S.M0 ≃ₗ[k] (gluedLinesSections k a b lam n m).M0)
        (e₁ : S.M1 ≃ₗ[k] (gluedLinesSections k a b lam n m).M1)
        (e₀₁ : S.M01 ≃ₗ[k] (gluedLinesSections k a b lam n m).M01),
        (∀ t, e₀₁ (S.r0 t) = (gluedLinesSections k a b lam n m).r0 (e₀ t)) ∧
        (∀ t, e₀₁ (S.r1 t) = (gluedLinesSections k a b lam n m).r1 (e₁ t)) := by sorry

-- Prove2me | Theorems.Thm_TwoChartCech_exists_semilinearEquiv_gluedLinesSections_of_invertible
-- name    : TwoChartCech.exists_semilinearEquiv_gluedLinesSections_of_invertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/f11e91bc-fc78-58cd-858e-8e9bdc665ebb
-- title:
--   Invertible sections on the glued-lines cover are the explicit model
-- statement:
--   Let $k$ be a field, $s \in \mathbb{N}$, and let $a, b : \mathrm{Fin}\,s \to k^{\times}$ be injective families of units. Let $\mathcal{U}$ be a two-chart cover over $k$, that is, $k$-algebras $A_0, A_1, A_{01}$ together with $k$-algebra maps $\rho_0 : A_0 \to A_{01}$ and $\rho_1 : A_1 \to A_{01}$, and let $S$ be a sections datum on $\mathcal{U}$: an $A_0$-module $M_0$, an $A_1$-module $M_1$, an $A_{01}$-module $M_{01}$, each also a $k$-module compatibly with the respective scalar tower, and $k$-linear maps $r_0 : M_0 \to M_{01}$, $r_1 : M_1 \to M_{01}$ satisfying $r_j(a \cdot m) = \rho_j(a) \cdot r_j(m)$. Assume given $k$-algebra isomorphisms $\varphi_0, \varphi_1, \varphi_{01}$ from $A_0, A_1, A_{01}$ onto the chart rings of `gluedLinesCover k a b`, namely onto the subalgebra of $k[T;T^{-1}] \times k[T;T^{-1}]$ of pairs $(f,g)$ with $f(a_i) = g(b_i)$ for all $i$, intersected with the pairs whose components have only non-negative exponents (for $A_0$), only non-positive exponents (for $A_1$), or unrestricted (for $A_{01}$), and assume $\varphi_{01} \circ \rho_0 = \rho_0' \circ \varphi_0$ and $\varphi_{01} \circ \rho_1 = \rho_1' \circ \varphi_1$, where $\rho_0', \rho_1'$ are the inclusions of the model. Assume $M_0$ is invertible over $A_0$ and $M_1$ invertible over $A_1$. Then, viewing $A_{01}$ as an $A_0$- and as an $A_1$-algebra via $\rho_0$ and $\rho_1$, for every pair of $A_{01}$-linear isomorphisms $A_{01} \otimes_{A_0} M_0 \xrightarrow{\sim} M_{01}$ and $A_{01} \otimes_{A_1} M_1 \xrightarrow{\sim} M_{01}$ sending $1 \otimes t$ to $r_0(t)$, resp. $r_1(t)$, there exist integers $n, m$, units $\lambda : \mathrm{Fin}\,s \to k^{\times}$, and $k$-linear isomorphisms $e_0, e_1, e_{01}$ from $M_0, M_1, M_{01}$ onto the three modules of `gluedLinesSections k a b lam n m`, which consist of the pairs of Laurent polynomials satisfying the predicate `GluedCond a b lam` and, respectively, having both components with non-negative exponents, having $f_1 T^{-n}$ and $f_2 T^{-m}$ with non-positive exponents, or no further condition, such that $e_{01} \circ r_0$ and $e_{01} \circ r_1$ agree with the model inclusions composed with $e_0$ and $e_1$, and such that the three isomorphisms are semilinear over the $\varphi$'s: the underlying Laurent pair of $e_0(f \cdot t)$ is $\varphi_0(f)$ times that of $e_0(t)$, and likewise for $e_1$ with $\varphi_1$ and for $e_{01}$ with $\varphi_{01}$.
--
--   This is the recognition step for line bundles on a chain-type degeneration: an abstract invertible sections datum on a two-chart cover identified with the glued-lines cover (two projective lines glued along the $s$ pairs of points $a_i \sim b_i$) is, compatibly with the chart identifications, the explicit model datum of bidegree $(n,m)$ with gluing parameters $\lambda$. It is the model-side input to [`AlgebraicGeometry.TwoGluedProjectiveLines.exists_linearEquiv_sectionsOf_gluedLinesSections_and_eulerChar_pullback_of_isAlgClosed`](thm.html#AlgebraicGeometry.TwoGluedProjectiveLines.exists_linearEquiv_sectionsOf_gluedLinesSections_and_eulerChar_pullback_of_isAlgClosed), where the geometric side supplies the chart isomorphisms, the base-change isomorphisms on the overlap and the invertibility of the chart-wise sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_exists_semilinearEquiv_gluedLinesSections_of_invertible.lean

import Mathlib
import Definitions.Def_TwoChartCech_GluedLines

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TwoChartCech TensorProduct LaurentPolynomial

universe u

theorem TwoChartCech.exists_semilinearEquiv_gluedLinesSections_of_invertible
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
        (∀ t, e₀₁ (S.r1 t) = (gluedLinesSections k a b lam n m).r1 (e₁ t)) ∧
        (∀ (f : 𝒰.A0) (t : S.M0), (e₀ (f • t)).1 = (φ₀ f : k[T;T⁻¹] × k[T;T⁻¹]) * (e₀ t).1) ∧
        (∀ (f : 𝒰.A1) (t : S.M1), (e₁ (f • t)).1 = (φ₁ f : k[T;T⁻¹] × k[T;T⁻¹]) * (e₁ t).1) ∧
        (∀ (f : 𝒰.A01) (t : S.M01), (e₀₁ (f • t)).1 = (φ₀₁ f : k[T;T⁻¹] × k[T;T⁻¹]) * (e₀₁ t).1) := by sorry

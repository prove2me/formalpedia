-- Prove2me | Theorems.Thm_TwoChartCech_gluedLinesSections_nonempty_linearEquiv_structureSheaf_iff
-- name    : TwoChartCech.gluedLinesSections_nonempty_linearEquiv_structureSheaf_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/d88c0899-3671-5045-bc38-5cb2c02338ee
-- title:
--   Glued line bundle trivial iff n=m=0 and λ constant
-- statement:
--   Let $k$ be a field, $s$ a natural number, $a,b:\mathrm{Fin}\,s\to k^\times$ with $b$ injective, $\lambda:\mathrm{Fin}\,s\to k^\times$, and $n,m\in\mathbb Z$. Consider the two-chart cover `gluedLinesCover k a b`: its overlap algebra $A_{01}$ consists of the pairs $(f_1,f_2)\in k[T;T^{-1}]\times k[T;T^{-1}]$ with $f_1(a_i)=f_2(b_i)$ for all $i$ (evaluation at the units $a_i,b_i$), $A_0$ is the subalgebra of such pairs both of whose components have coefficients supported in nonnegative exponents, $A_1$ the one with both components supported in nonpositive exponents, and $\rho_0,\rho_1$ the inclusions. The sections datum `gluedLinesSections k a b lam n m` has $M_{01}$ the $A_{01}$-submodule of pairs satisfying the predicate `GluedCond a b lam` (the node-gluing condition twisted by $\lambda$), $M_0$ those among them with both components supported in nonnegative exponents, $M_1$ those with $f_1T^{-n}$ and $f_2T^{-m}$ supported in nonpositive exponents, and $r_0,r_1$ the inclusions into $M_{01}$. The theorem asserts: there exist $A_0$-, $A_1$- and $A_{01}$-linear equivalences $g_0:M_0\simeq A_0$, $g_1:M_1\simeq A_1$, $g_{01}:M_{01}\simeq A_{01}$ with $g_{01}\circ r_0=\rho_0\circ g_0$ and $g_{01}\circ r_1=\rho_1\circ g_1$, if and only if $n=0$, $m=0$ and $\lambda_i=\lambda_j$ for all $i,j$.
--
--   This is the triviality criterion for the line bundle of bidegree $(n,m)$ with gluing data $\lambda$ on two projective lines glued at the $s$ pairs of points $a_i\sim b_i$, stated at the level of the explicit two-chart Čech datum: such a bundle is isomorphic to the structure sheaf exactly when both degrees vanish and the gluing parameter is constant. It is used in the computation of Euler characteristics and pullbacks of line bundles on two glued projective lines over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_gluedLinesSections_nonempty_linearEquiv_structureSheaf_iff.lean

import Mathlib
import Definitions.Def_TwoChartCech_GluedLines

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

universe u

open LaurentPolynomial TwoChartCech

theorem TwoChartCech.gluedLinesSections_nonempty_linearEquiv_structureSheaf_iff (k : Type u) [Field k] {s : ℕ}
    (a b : Fin s → kˣ) (hb : Function.Injective b) (lam : Fin s → kˣ) (n m : ℤ) :
    letI := (gluedLinesSections k a b lam n m).M0_moduleA
    letI := (gluedLinesSections k a b lam n m).M1_moduleA
    letI := (gluedLinesSections k a b lam n m).M01_moduleA
    (∃ (g₀ : (gluedLinesSections k a b lam n m).M0 ≃ₗ[(gluedLinesCover k a b).A0] (gluedLinesCover k a b).structureSheaf.M0)
       (g₁ : (gluedLinesSections k a b lam n m).M1 ≃ₗ[(gluedLinesCover k a b).A1] (gluedLinesCover k a b).structureSheaf.M1)
       (g₀₁ : (gluedLinesSections k a b lam n m).M01 ≃ₗ[(gluedLinesCover k a b).A01] (gluedLinesCover k a b).structureSheaf.M01),
       (∀ t, g₀₁ ((gluedLinesSections k a b lam n m).r0 t) = (gluedLinesCover k a b).structureSheaf.r0 (g₀ t)) ∧
       (∀ t, g₀₁ ((gluedLinesSections k a b lam n m).r1 t) = (gluedLinesCover k a b).structureSheaf.r1 (g₁ t)))
     ↔ (n = 0 ∧ m = 0 ∧ ∀ i j, lam i = lam j) := by sorry

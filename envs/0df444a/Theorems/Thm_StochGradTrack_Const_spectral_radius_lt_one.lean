-- Prove2me | Theorems.Thm_StochGradTrack_Const_spectral_radius_lt_one
-- name    : StochGradTrack.Const.spectral_radius_lt_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:37.28021+00:00
-- url     : https://prove2.me/theorems/ac79c911-90a4-4058-8f43-6c5156c84928
-- title:
--   §3.1, p. 422 — under (23)–(25), det(I − A) ≥ ((Γ − 1)/(Γ + 1))(1 − a₁₁)(1 − a₂₂)(1 − a₃₃) > 0 and ρ(A) < 1
-- statement:
--   Let $\Gamma>1$, $\alpha>0$, $\mu>0$ with $\alpha\mu<1$, $L>0$, $n>0$, $0<\rho<1$, $w\ge0$ and $\beta>0$, and let $\mathbf A=[a_{ij}]$ be the matrix of (21) with $\rho_w=\rho$ and $\|\mathbf W-\mathbf I\|=w$. Suppose
--   $$a_{33}=(1+4\alpha L+2\alpha^2L^2+\beta)\rho^2=\frac{1+\rho^2}{2},\tag{23}$$
--   $$a_{23}a_{32}\le\frac1\Gamma(1-a_{22})(1-a_{33}),\tag{24}$$
--   $$a_{12}a_{23}a_{31}\le\frac{1}{\Gamma+1}(1-a_{11})\big[(1-a_{22})(1-a_{33})-a_{23}a_{32}\big].\tag{25}$$
--   Then
--   $$\det(\mathbf I-\mathbf A)\ge\frac{\Gamma-1}{\Gamma+1}(1-a_{11})(1-a_{22})(1-a_{33})>0,$$
--   and the spectral radius of $\mathbf A$ satisfies $\rho(\mathbf A)<1$.
--
--   This is the step that reduces stability of the linear system to the three scalar relations (23)–(25), which (7) is designed to guarantee.
--
--   **Formalization Note.** Lean indexes entries from $0$, so $a_{ij}$ is `A (i-1) (j-1)`. The hypothesis $\alpha\mu<1$ is stated explicitly (under the goal's assumptions it follows from (7) and $\mu\le L$); it makes $\mathbf A$ nonnegative. The spectral radius is over $\mathbb C$. $a_{33}<1$ in (23) follows from $\rho<1$.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), §3.1, (23)–(25), p. 421 and the det(I − A) display, p. 422

import Mathlib
import Definitions.Def_StochGradTrack_Const_Matrix

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem spectral_radius_lt_one (Γ α β μ L n ρ w : ℝ) (hΓ : 1 < Γ) (hα : 0 < α)
    (hαμ : α * μ < 1) (hμ : 0 < μ) (hL : 0 < L) (hn : 0 < n) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hw : 0 ≤ w) (hβ : 0 < β)
    (h23 : (Agen α β μ L n ρ w) 2 2 = (1 + ρ ^ 2) / 2)
    (h24 : (Agen α β μ L n ρ w) 1 2 * (Agen α β μ L n ρ w) 2 1
      ≤ 1 / Γ * (1 - (Agen α β μ L n ρ w) 1 1) * (1 - (Agen α β μ L n ρ w) 2 2))
    (h25 : (Agen α β μ L n ρ w) 0 1 * (Agen α β μ L n ρ w) 1 2 * (Agen α β μ L n ρ w) 2 0
      ≤ 1 / (Γ + 1) * (1 - (Agen α β μ L n ρ w) 0 0)
        * ((1 - (Agen α β μ L n ρ w) 1 1) * (1 - (Agen α β μ L n ρ w) 2 2) - (Agen α β μ L n ρ w) 1 2 * (Agen α β μ L n ρ w) 2 1)) :
    (Γ - 1) / (Γ + 1) * (1 - (Agen α β μ L n ρ w) 0 0) * (1 - (Agen α β μ L n ρ w) 1 1) * (1 - (Agen α β μ L n ρ w) 2 2)
        ≤ (1 - Agen α β μ L n ρ w).det ∧
      0 < (1 - Agen α β μ L n ρ w).det ∧
      spectralRadius ℂ ((Agen α β μ L n ρ w).map (algebraMap ℝ ℂ)) < 1 := by sorry

end StochGradTrack.Const

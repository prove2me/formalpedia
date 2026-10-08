-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_eq_109_111
-- name    : SpikedWishart.SoftEdge.eq_109_111
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:40:04.321366+00:00
-- url     : https://prove2.me/theorems/1aeec7b2-0ab6-4070-ba7e-44ec82de7206
-- title:
--   (109), (111), pp. 1661–1662 — p_c = γ/(γ+1) is a double critical point of f, and f‴(p_c) = 2(γ+1)⁴/γ³ = 2ν³
-- statement:
--   Let $\gamma\ge1$ and $q\in\mathbb R$, let $\mu=\big(\frac{1+\gamma}{\gamma}\big)^2$, $\nu=\frac{(1+\gamma)^{4/3}}{\gamma}$, $p_c=\frac{\gamma}{\gamma+1}$, and
--   $$
--   f(z)=-\mu(z-q)+\log z-\frac1{\gamma^2}\log(1-z)
--   $$
--   with the principal branch of $\log$. Then
--
--   1. (109) $f'(p_c)=f''(p_c)=0$;
--   2. (111) $f^{(3)}(z)=\dfrac2{z^3}-\dfrac2{\gamma^2(z-1)^3}$ for every $z$ with $z$ and $1-z$ off $(-\infty,0]$;
--   3. (111) $f^{(3)}(p_c)=\dfrac{2(\gamma+1)^4}{\gamma^3}=2\nu^3$.
--
--   The choice of $\mu$ makes $p_c$ a double saddle point of the phase function, which is what produces the cubic exponent $e^{a^3/3}$ and the $M^{2/3}$ scaling of Theorem 1.1(a).
--
--   **Formalization Note** Derivatives are complex derivatives of the complex function $f$; at $p_c\in(0,1)$ both logarithms are holomorphic.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1661–1662, §3, (101), (105)–(111)

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex

namespace SpikedWishart.SoftEdge

theorem eq_109_111 (γ q : ℝ) (hγ : 1 ≤ γ) :
    deriv (fFn γ q) (pc γ) = 0 ∧
      iteratedDeriv 2 (fFn γ q) (pc γ) = 0 ∧
      (∀ z : ℂ, z ∈ slitPlane → 1 - z ∈ slitPlane →
        iteratedDeriv 3 (fFn γ q) z = 2 / z ^ 3 - 2 / ((γ : ℂ) ^ 2 * (z - 1) ^ 3)) ∧
      iteratedDeriv 3 (fFn γ q) (pc γ) = ((2 * (γ + 1) ^ 4 / γ ^ 3 : ℝ) : ℂ) ∧
      2 * (γ + 1) ^ 4 / γ ^ 3 = 2 * nu γ ^ 3 := by sorry

end SpikedWishart.SoftEdge

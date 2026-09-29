-- Prove2me | Theorems.Thm_SchwartzMap_exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one
-- name    : SchwartzMap.exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/e5db3119-d076-53d7-97e3-0570846e0245
-- title:
--   A compactly supported Schwartz bump on a finite-dimensional real space
-- statement:
--   Let $E$ be a real normed additive commutative group equipped with a real normed space structure which is finite-dimensional over $\mathbb{R}$. The assertion is that there exists an element $g$ of the space $\mathcal{S}(E,\mathbb{C})$ of complex-valued Schwartz functions on $E$ (written `𝓢(E, ℂ)`) with the following four properties simultaneously: the function $g$ has compact support, i.e. the closure of its support is compact; at every point $x \in E$ the value $g(x)$ has non-negative real part and vanishing imaginary part, so $g$ takes values in the non-negative reals; at every point $x$ one has $\lVert g(x) \rVert \le 1$; $g(x) = 1$ for every $x$ with $\lVert x \rVert \le 1$; and $g(x) = 0$ for every $x$ with $2 \le \lVert x \rVert$. Thus $g$ is a Schwartz function with values in $[0,1] \subseteq \mathbb{R} \subseteq \mathbb{C}$, identically $1$ on the closed unit ball and identically $0$ outside the open ball of radius $2$.
--
--   This is the standard archimedean bump function, used to manufacture test functions on adelic spaces as a product of such a factor at the archimedean places with a characteristic function of a compact open set at the finite places. It is cited in the construction of an element of a Schwartz–Bruhat space used to study the behaviour of a zeta integral near the edge of its region of convergence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_SchwartzMap_exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped SchwartzMap

theorem SchwartzMap.exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ g : 𝓢(E, ℂ), HasCompactSupport g ∧ (∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) ∧ (∀ x, ‖g x‖ ≤ 1) ∧
      (∀ x, ‖x‖ ≤ 1 → g x = 1) ∧ (∀ x, 2 ≤ ‖x‖ → g x = 0) := by sorry

-- Prove2me | Theorems.Thm_PhragmenLindelof_exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip
-- name    : PhragmenLindelof.exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/40726dc6-1347-574d-9c62-e0dd6538fc48
-- title:
--   Phragmén–Lindelöf in a strip, polynomial form
-- statement:
--   Let $a<b$ be real numbers and let $\alpha\ge 0$. Then there exists a real constant $C>0$ (depending only on $a$, $b$, $\alpha$) such that for every function $f\colon\mathbb{C}\to\mathbb{C}$ and every real $M\ge 0$ the following holds. Assume $f$ is differentiable on the open vertical strip $\{z: a<\operatorname{Re}z<b\}$ and continuous on its closure, in the sense of `DiffContOnCl`; assume the Phragmén–Lindelöf growth condition, namely that there are reals $c<\pi/(b-a)$ and $B$ with $\|f(z)\|\le\exp\bigl(B\exp(c|\operatorname{Im}z|)\bigr)$ for all $z$ with $a<\operatorname{Re}z<b$; and assume the boundary bounds $\|f(z)\|\le M(1+|\operatorname{Im}z|)^{\alpha}$ at every $z$ with $\operatorname{Re}z=a$ and at every $z$ with $\operatorname{Re}z=b$ (the power being the real `rpow`). Then $\|f(z)\|\le C\,M\,(1+|\operatorname{Im}z|)^{\alpha}$ for every $z$ with $a\le\operatorname{Re}z\le b$. The order of the quantifiers is the point: the single constant $C$ is chosen before $f$ and $M$, hence is uniform in both.
--
--   This is the equal-exponent, polynomial-growth form of the Phragmén–Lindelöf convexity principle for a vertical strip, with a constant uniform in the function and in the boundary bound. It is used in the Tate-style analytic development of Hecke $L$-functions and the Dedekind zeta function, where it supplies growth bounds in vertical strips for analytically continued partial Euler products and for $(s-1)$ times the Dedekind zeta function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PhragmenLindelof_exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PhragmenLindelof.exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip
    (a b α : ℝ) (hab : a < b) (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℂ → ℂ) (M : ℝ), 0 ≤ M →
        DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b) →
        (∃ c : ℝ, c < Real.pi / (b - a) ∧ ∃ B : ℝ, ∀ z : ℂ, a < z.re → z.re < b →
            ‖f z‖ ≤ Real.exp (B * Real.exp (c * |z.im|))) →
        (∀ z : ℂ, z.re = a → ‖f z‖ ≤ M * (1 + |z.im|) ^ α) →
        (∀ z : ℂ, z.re = b → ‖f z‖ ≤ M * (1 + |z.im|) ^ α) →
        ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ C * M * (1 + |z.im|) ^ α := by sorry

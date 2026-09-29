-- Prove2me | Theorems.Thm_StickyKakeya4_exact_collision_identity
-- name    : StickyKakeya4.exact_collision_identity
-- status  : Proved
-- author  : @sensei
-- created : 2026-09-26T03:04:43.792638+00:00
-- url     : https://prove2.me/theorems/85f39f69-2276-4ca7-9969-606db6aa8897
-- title:
--   Exact Pythagorean collision identity
-- statement:
--   For nonzero $\alpha\in\mathbb R^3$ and arbitrary $\beta\in\mathbb R^3$, let $s_*=-\langle\alpha,\beta\rangle/\|\alpha\|^2$ and $r=\beta+s_*\alpha$.  Then, for every real $s$,
--
--   $$
--   \|\beta+s\alpha\|^2=\|r\|^2+\|\alpha\|^2|s-s_*|^2.
--   $$
--
--   This separates collision displacement exactly into normal residual and longitudinal Reeb-time offset.
-- source:
--   Chenxi Cai, source manuscript https://cchx0000.github.io/papers/sticky-kakeya-contact-symplectic/sticky-kakeya-contact-symplectic.pdf, Definition 4.12 and Lemma 4.13.

import Definitions.Def_sticky_kakeya4_core

open scoped RealInnerProductSpace

namespace StickyKakeya4

theorem exact_collision_identity (α β : E3) (hα : α ≠ 0) (s : ℝ) :
    ‖β + s • α‖ ^ 2 =
      ‖collisionResidual α β‖ ^ 2 + ‖α‖ ^ 2 * |s - collisionTime α β| ^ 2 := by sorry

end StickyKakeya4

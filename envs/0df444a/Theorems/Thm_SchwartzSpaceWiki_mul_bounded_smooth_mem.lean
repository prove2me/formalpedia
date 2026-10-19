-- Prove2me | Theorems.Thm_SchwartzSpaceWiki_mul_bounded_smooth_mem
-- name    : SchwartzSpaceWiki.mul_bounded_smooth_mem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:16:36.646668+00:00
-- url     : https://prove2.me/theorems/e52d83c7-2b84-4aad-b56f-387e6ed02053
-- title:
--   Schwartz function times bounded smooth function
-- statement:
--   Let $f\in\mathcal{S}(\mathbb{R}^n)$ and let $g:\mathbb{R}^n\to\mathbb{C}$ be a smooth function which is bounded together with its derivatives of all orders, i.e. for every multi-index $\beta$ there is $C_\beta$ with $|D^\beta g(x)|\le C_\beta$ for all $x$ (the case $\beta=0$ says $g$ is bounded). Then $fg\in\mathcal{S}(\mathbb{R}^n)$.
-- source:
--   Wikipedia, "Schwartz space", revision oldid=1360762580 (https://en.wikipedia.org/w/index.php?title=Schwartz_space&oldid=1360762580), section "Properties — Analytic properties", 2nd bullet

import Mathlib
import Definitions.Def_SchwartzSpaceWiki_Defs

open MeasureTheory

namespace SchwartzSpaceWiki

theorem mul_bounded_smooth_mem (n : ℕ) (f g : Rn n → ℂ) (hf : f ∈ schwartzSpace n)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hbdd : ∀ β : MultiIndex n, ∃ C : ℝ, ∀ x : Rn n, ‖iteratedPartialDeriv β g x‖ ≤ C) :
    f * g ∈ schwartzSpace n := by sorry

end SchwartzSpaceWiki

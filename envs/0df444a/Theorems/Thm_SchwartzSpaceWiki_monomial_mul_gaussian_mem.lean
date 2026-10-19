-- Prove2me | Theorems.Thm_SchwartzSpaceWiki_monomial_mul_gaussian_mem
-- name    : SchwartzSpaceWiki.monomial_mul_gaussian_mem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:13:23.656026+00:00
-- url     : https://prove2.me/theorems/1af72413-1a99-4947-8a40-743f548c5e7d
-- title:
--   $x^\alpha e^{-a|x|^2}\in\mathcal{S}(\mathbb{R}^n)$
-- statement:
--   For every multi-index $\alpha\in\mathbb{N}^n$ and every real number $a>0$, the function $x\mapsto x^\alpha e^{-a|x|^2}$ belongs to $\mathcal{S}(\mathbb{R}^n)$.
-- source:
--   Wikipedia, "Schwartz space", revision oldid=1360762580 (https://en.wikipedia.org/w/index.php?title=Schwartz_space&oldid=1360762580), section "Examples of functions in the Schwartz space", 1st bullet

import Mathlib
import Definitions.Def_SchwartzSpaceWiki_Defs

open MeasureTheory

namespace SchwartzSpaceWiki

theorem monomial_mul_gaussian_mem (n : ℕ) (α : MultiIndex n) (a : ℝ) (ha : 0 < a) :
    (fun x : Rn n => (monomial α x : ℂ) * Complex.exp (-(a * ‖x‖ ^ 2 : ℝ))) ∈
      schwartzSpace n := by sorry

end SchwartzSpaceWiki

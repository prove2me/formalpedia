-- Prove2me | Theorems.Thm_SchwartzSpaceWiki_mul_mem
-- name    : SchwartzSpaceWiki.mul_mem
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T00:15:54.746607+00:00
-- url     : https://prove2.me/theorems/ebaa8d93-921c-4adc-8f23-137ed769cf81
-- title:
--   $\mathcal{S}(\mathbb{R}^n)$ is closed under multiplication
-- statement:
--   If $f,g\in\mathcal{S}(\mathbb{R}^n)$, then their pointwise product $fg$ belongs to $\mathcal{S}(\mathbb{R}^n)$. Together with the vector-space property, this makes $\mathcal{S}(\mathbb{R}^n)$ an algebra.
-- source:
--   Wikipedia, "Schwartz space", revision oldid=1360762580 (https://en.wikipedia.org/w/index.php?title=Schwartz_space&oldid=1360762580), section "Properties — Analytic properties", 1st bullet

import Mathlib
import Definitions.Def_SchwartzSpaceWiki_Defs

open MeasureTheory

namespace SchwartzSpaceWiki

theorem mul_mem (n : ℕ) (f g : Rn n → ℂ) (hf : f ∈ schwartzSpace n)
    (hg : g ∈ schwartzSpace n) :
    f * g ∈ schwartzSpace n := by sorry

end SchwartzSpaceWiki

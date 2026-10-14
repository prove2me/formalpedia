-- Prove2me | Theorems.Thm_SchwartzSpaceWiki_contDiff_hasCompactSupport_mem
-- name    : SchwartzSpaceWiki.contDiff_hasCompactSupport_mem
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T00:13:49.593277+00:00
-- url     : https://prove2.me/theorems/a675ab3e-f6c9-40c6-a8c1-666410ab2841
-- title:
--   $C_c^\infty(\mathbb{R}^n)\subseteq\mathcal{S}(\mathbb{R}^n)$
-- statement:
--   Every smooth function $f:\mathbb{R}^n\to\mathbb{C}$ with compact support belongs to $\mathcal{S}(\mathbb{R}^n)$. Equivalently, the space $C_c^\infty(\mathbb{R}^n)$ of bump functions is contained in $\mathcal{S}(\mathbb{R}^n)$.
-- source:
--   Wikipedia, "Schwartz space", revision oldid=1360762580 (https://en.wikipedia.org/w/index.php?title=Schwartz_space&oldid=1360762580), section "Examples of functions in the Schwartz space", 2nd bullet, and section "Relation of Schwartz spaces with other topological vector spaces", 2nd bullet

import Mathlib
import Definitions.Def_SchwartzSpaceWiki_Defs

open MeasureTheory

namespace SchwartzSpaceWiki

theorem contDiff_hasCompactSupport_mem (n : ℕ) (f : Rn n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsupp : HasCompactSupport f) :
    f ∈ schwartzSpace n := by sorry

end SchwartzSpaceWiki

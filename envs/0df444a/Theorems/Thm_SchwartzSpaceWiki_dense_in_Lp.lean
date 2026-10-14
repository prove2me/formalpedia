-- Prove2me | Theorems.Thm_SchwartzSpaceWiki_dense_in_Lp
-- name    : SchwartzSpaceWiki.dense_in_Lp
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T00:17:45.150998+00:00
-- url     : https://prove2.me/theorems/c9a2d698-315e-4b1d-8d91-57280912c402
-- title:
--   $\mathcal{S}(\mathbb{R}^n)$ is dense in $L^p(\mathbb{R}^n)$, $1\le p<\infty$
-- statement:
--   Let $1\le p<\infty$. Then $\mathcal{S}(\mathbb{R}^n)\subseteq L^p(\mathbb{R}^n)$ (every Schwartz function is $p$-integrable for Lebesgue measure), and $\mathcal{S}(\mathbb{R}^n)$ is dense in $L^p(\mathbb{R}^n)$: for every $g\in L^p(\mathbb{R}^n)$ and every $\varepsilon>0$ there is $f\in\mathcal{S}(\mathbb{R}^n)$ with $\|g-f\|_{L^p}<\varepsilon$.
-- source:
--   Wikipedia, "Schwartz space", revision oldid=1360762580 (https://en.wikipedia.org/w/index.php?title=Schwartz_space&oldid=1360762580), section "Relation of Schwartz spaces with other topological vector spaces", 1st bullet

import Mathlib
import Definitions.Def_SchwartzSpaceWiki_Defs

open MeasureTheory

namespace SchwartzSpaceWiki

theorem dense_in_Lp (n : ℕ) (p : ENNReal) (hp1 : 1 ≤ p) (hptop : p ≠ ⊤) :
    (∀ f ∈ schwartzSpace n, MemLp f p (volume : Measure (Rn n))) ∧
    (∀ g : Rn n → ℂ, MemLp g p (volume : Measure (Rn n)) →
      ∀ ε : ENNReal, 0 < ε →
        ∃ f ∈ schwartzSpace n, eLpNorm (g - f) p (volume : Measure (Rn n)) < ε) := by sorry

end SchwartzSpaceWiki

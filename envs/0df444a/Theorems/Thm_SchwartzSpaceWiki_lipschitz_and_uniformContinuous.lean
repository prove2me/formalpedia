-- Prove2me | Theorems.Thm_SchwartzSpaceWiki_lipschitz_and_uniformContinuous
-- name    : SchwartzSpaceWiki.lipschitz_and_uniformContinuous
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T00:17:13.749625+00:00
-- url     : https://prove2.me/theorems/71ca4bdb-1aff-44c1-888b-7c0f407a0163
-- title:
--   Schwartz functions are Lipschitz and uniformly continuous
-- statement:
--   Every $f\in\mathcal{S}(\mathbb{R}^n)$ is Lipschitz continuous on $\mathbb{R}^n$ (there is $K\ge 0$ with $|f(x)-f(y)|\le K|x-y|$ for all $x,y$), and hence uniformly continuous on $\mathbb{R}^n$.
-- source:
--   Wikipedia, "Schwartz space", revision oldid=1360762580 (https://en.wikipedia.org/w/index.php?title=Schwartz_space&oldid=1360762580), section "Properties — Analytic properties", 4th bullet

import Mathlib
import Definitions.Def_SchwartzSpaceWiki_Defs

open MeasureTheory

namespace SchwartzSpaceWiki

theorem lipschitz_and_uniformContinuous (n : ℕ) (f : Rn n → ℂ) (hf : f ∈ schwartzSpace n) :
    (∃ K : NNReal, LipschitzWith K f) ∧ UniformContinuous f := by sorry

end SchwartzSpaceWiki

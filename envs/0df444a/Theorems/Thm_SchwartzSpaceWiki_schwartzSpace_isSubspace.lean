-- Prove2me | Theorems.Thm_SchwartzSpaceWiki_schwartzSpace_isSubspace
-- name    : SchwartzSpaceWiki.schwartzSpace_isSubspace
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T00:12:57.677986+00:00
-- url     : https://prove2.me/theorems/29d6f91d-8107-4025-a9df-69b173c1caf8
-- title:
--   $\mathcal{S}(\mathbb{R}^n)$ is a complex vector space
-- statement:
--   The Schwartz space $\mathcal{S}(\mathbb{R}^n,\mathbb{C})$ is a complex linear subspace of $C^\infty(\mathbb{R}^n,\mathbb{C})$: it contains the zero function, and for all $f,g\in\mathcal{S}(\mathbb{R}^n)$ and $c\in\mathbb{C}$ we have $f+g\in\mathcal{S}(\mathbb{R}^n)$ and $cf\in\mathcal{S}(\mathbb{R}^n)$.
-- source:
--   Wikipedia, "Schwartz space", revision oldid=1360762580 (https://en.wikipedia.org/w/index.php?title=Schwartz_space&oldid=1360762580), section "Definition" ("is a subspace of C^∞") and section "Examples", 3rd bullet ("Because the Schwartz space is a vector space")

import Mathlib
import Definitions.Def_SchwartzSpaceWiki_Defs

open MeasureTheory

namespace SchwartzSpaceWiki

theorem schwartzSpace_isSubspace (n : ℕ) :
    (0 : Rn n → ℂ) ∈ schwartzSpace n ∧
    (∀ f ∈ schwartzSpace n, ∀ g ∈ schwartzSpace n, f + g ∈ schwartzSpace n) ∧
    (∀ (c : ℂ), ∀ f ∈ schwartzSpace n, c • f ∈ schwartzSpace n) := by sorry

end SchwartzSpaceWiki

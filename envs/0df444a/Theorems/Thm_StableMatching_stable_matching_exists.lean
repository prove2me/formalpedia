-- Prove2me | Theorems.Thm_StableMatching_stable_matching_exists
-- name    : StableMatching.stable_matching_exists
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T13:34:00.436699+00:00
-- url     : https://prove2.me/theorems/a00036b0-6279-4eb4-8907-f45fd6b30788
-- title:
--   Existence of stable matchings
-- statement:
--   For every instance with $n$ men and $n$ women, each ranking all members of the other side strictly, there exists a stable matching: a bijection $\mu$ from men to women with no pair $(m,w)$ such that $m$ prefers $w$ to $\mu(m)$ and $w$ prefers $m$ to $\mu^{-1}(w)$.
-- source:
--   Wikipedia, "Stable matching problem" (https://en.wikipedia.org/wiki/Stable_matching_problem), sections "Stable matching problem" (introduction), "Different stable matchings" and "Algorithmic solution"; primary reference: D. Gale, L. S. Shapley, College Admissions and the Stability of Marriage, Amer. Math. Monthly 69 (1962) 9–14, doi:10.2307/2312726.

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem stable_matching_exists {n : ℕ} (I : Instance n) :
    ∃ μ : Matching n, I.IsStable μ := by sorry

end StableMatching

-- Prove2me | Theorems.Thm_StableMatching_galeShapley_stable
-- name    : StableMatching.galeShapley_stable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T13:31:29.279989+00:00
-- url     : https://prove2.me/theorems/917d8e35-dab6-47b7-83a2-828c972ed7a5
-- title:
--   Gale–Shapley: the algorithm produces a stable matching
-- statement:
--   For every instance $I$ with $n$ men and $n$ women (strict preference lists), the Gale–Shapley (men-proposing deferred acceptance) algorithm is guaranteed to produce a stable matching: there is a bijection $\mu$ from men to women such that, after the algorithm's $n^2$ rounds, every man $m$ is engaged to $\mu(m)$, and $\mu$ has no blocking pair, i.e. there are no $m, w$ with $m$ preferring $w$ to $\mu(m)$ and $w$ preferring $m$ to $\mu^{-1}(w)$.
-- source:
--   Wikipedia, "Stable matching problem" (https://en.wikipedia.org/wiki/Stable_matching_problem), sections "Stable matching problem" (introduction), "Different stable matchings" and "Algorithmic solution"; primary reference: D. Gale, L. S. Shapley, College Admissions and the Stability of Marriage, Amer. Math. Monthly 69 (1962) 9–14, doi:10.2307/2312726.

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_stable {n : ℕ} (I : Instance n) :
    ∃ μ : Matching n, I.IsGSOutcome μ ∧ I.IsStable μ := by sorry

end StableMatching

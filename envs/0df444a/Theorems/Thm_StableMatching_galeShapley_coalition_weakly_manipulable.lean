-- Prove2me | Theorems.Thm_StableMatching_galeShapley_coalition_weakly_manipulable
-- name    : StableMatching.galeShapley_coalition_weakly_manipulable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T13:43:37.468042+00:00
-- url     : https://prove2.me/theorems/789a3b43-53ad-4ca3-9468-501565aacdc0
-- title:
--   Some coalition of men can weakly manipulate Gale–Shapley
-- statement:
--   There exist $n$, instances $I$ and $I'$ with $n$ men and $n$ women, and a set $C$ of men such that $I'$ differs from $I$ only in the preference lists of men in $C$, and, with $\mu$ and $\mu'$ the Gale–Shapley outcomes of $I$ and $I'$: every man $m \in C$ either keeps the same partner ($\mu'(m) = \mu(m)$) or strictly prefers $\mu'(m)$ to $\mu(m)$ according to his true list in $I$, and at least one man of $C$ strictly prefers $\mu'(m)$ to $\mu(m)$.
-- source:
--   Wikipedia, "Stable matching problem" (https://en.wikipedia.org/wiki/Stable_matching_problem), sections "Stable matching problem" (introduction), "Different stable matchings" and "Algorithmic solution"; primary reference: D. Gale, L. S. Shapley, College Admissions and the Stability of Marriage, Amer. Math. Monthly 69 (1962) 9–14, doi:10.2307/2312726.

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_coalition_weakly_manipulable :
    ∃ (n : ℕ) (I I' : Instance n) (C : Finset (Fin n)) (μ μ' : Matching n),
      I.MenDeviation I' C ∧ I.IsGSOutcome μ ∧ I'.IsGSOutcome μ' ∧
      (∀ m ∈ C, μ' m = μ m ∨ I.manPrefers m (μ' m) (μ m)) ∧
      ∃ m ∈ C, I.manPrefers m (μ' m) (μ m) := by sorry

end StableMatching

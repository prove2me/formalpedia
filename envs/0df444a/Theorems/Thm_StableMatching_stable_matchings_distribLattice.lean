-- Prove2me | Theorems.Thm_StableMatching_stable_matchings_distribLattice
-- name    : StableMatching.stable_matchings_distribLattice
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T13:45:03.749856+00:00
-- url     : https://prove2.me/theorems/ac203a16-b807-4893-885e-d30f6e638106
-- title:
--   Stable matchings form a finite distributive lattice
-- statement:
--   For every instance with $n$ men and $n$ women, there is a distributive lattice structure on the (finite) set of stable matchings whose order is: $\mu \le \nu$ iff every man $m$ weakly prefers $\mu(m)$ to $\nu(m)$, i.e. $\mathrm{manRank}_m(\mu(m)) \le \mathrm{manRank}_m(\nu(m))$ for all $m$.
-- source:
--   Wikipedia, "Stable matching problem" (https://en.wikipedia.org/wiki/Stable_matching_problem), sections "Stable matching problem" (introduction), "Different stable matchings" and "Algorithmic solution"; primary reference: D. Gale, L. S. Shapley, College Admissions and the Stability of Marriage, Amer. Math. Monthly 69 (1962) 9–14, doi:10.2307/2312726.

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem stable_matchings_distribLattice {n : ℕ} (I : Instance n) :
    ∃ L : DistribLattice {μ : Matching n // I.IsStable μ},
      ∀ μ ν : {μ : Matching n // I.IsStable μ},
        L.le μ ν ↔ ∀ m : Fin n, I.manRank m (μ.1 m) ≤ I.manRank m (ν.1 m) := by sorry

end StableMatching

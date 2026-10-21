-- Prove2me | Theorems.Thm_PolyClinch_TwoSided_theorem_3_11
-- name    : PolyClinch.TwoSided.theorem_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:17.351215+00:00
-- url     : https://prove2.me/theorems/e33f1ec6-a77a-46c2-83f7-1b61772e5674
-- title:
--   Theorem 3.11, p. 13 — Mechanism 2 satisfies (PO)
-- statement:
--   Let $\mathcal I$ be valid public information, $\varepsilon>0$, and $v\in(\varepsilon\mathbb N)^N$ the buyers' true valuations; let $\mathcal I^*$ be $\mathcal I$ with all bids replaced by $v$. If $\mathcal A$ is an output of Mechanism 2 on $\mathcal I^*$, then there is no allocation $\mathcal A'=(w',p',r')$ (so $w'|_{E_j}\in P_j$ and $p'_i\le B_i$) with $\sum_i p'_i\ge\sum_j r'_j$ such that
--   $$
--   u_i(\mathcal A)\le u_i(\mathcal A')\ (i\in N),\qquad u_j(\mathcal A)\le u_j(\mathcal A')\ (j\in M),
--   $$
--   with at least one of these inequalities strict.
--
--   "Our mechanism" in the page's sentence is Mechanism 2: the preceding sentence announces "(PO) for mechanism 2".
--
--   **Formalization Note** Outputs are any allocations in the relation `Mech2Outcome`. The competitor must be a feasible allocation of the original market.
-- source:
--   Hirai & Sato, Polyhedral Clinching Auctions for Two-sided Markets, arXiv:1708.04881v2, p. 13, Theorem 3.11; proof in §5.3, pp. 28–30

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Clinching

namespace PolyClinch.TwoSided

/-- Theorem 3.11 (Hirai–Sato p. 13). Mechanism 2 satisfies (PO): for a valid input `I` and true
valuations `val` on the `ε`-grid, no output of Mechanism 2 on `I*` (all bids replaced by `val`)
is Pareto-dominated by an allocation. -/
theorem theorem_3_11 {n m : ℕ} (E : Finset (Fin n × Fin m)) (ε : ℝ) (hε : 0 < ε)
    (I : PublicInfo E) (hI : Valid E ε I) (val : Fin n → ℝ) (hval : ∀ i, OnGrid ε (val i))
    (A : Allocation E) (hA : Mech2Outcome E (withBids E I val) ε A) :
    ¬ ParetoImprovable E I val A := by sorry

end PolyClinch.TwoSided

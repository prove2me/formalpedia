-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_source_budget
-- name    : ResourceScheduling.Graph.source_budget
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T14:26:28.359951+00:00
-- url     : https://prove2.me/theorems/32b5c7ba-476c-4e9d-b5bb-10de4833671a
-- title:
--   source budget
-- statement:
--   A structural register-program cost with a quadratic numeric bound, together with the linear output-transfer cost, is bounded by one Cook polynomial deadline for every input length.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_defs

namespace ResourceScheduling.Graph
theorem source_budget (A d : ℕ) (hd : 2 ≤ d) : ∃ k, ∀ L c o : ℕ,
    c ≤ A * (100 * (L + 1)^2 + 1)^d → o ≤ 5 * L^2 + 8 → c + 3 * o + 2 ≤ L^k + k := by sorry
end ResourceScheduling.Graph

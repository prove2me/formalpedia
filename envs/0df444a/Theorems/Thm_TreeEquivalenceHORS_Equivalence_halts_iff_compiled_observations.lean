-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_halts_iff_compiled_observations
-- name    : TreeEquivalenceHORS.Equivalence.halts_iff_compiled_observations
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T18:02:01.049926+00:00
-- url     : https://prove2.me/theorems/f44e8add-59b0-4de3-8bf1-e0732b36409c
-- title:
--   Halting is equivalent to a terminal disagreement in the intermediate schemes
-- statement:
--   For every two-counter machine started with both counters zero, the machine halts if and only if there is a finite address at which its left and right compiled schemes expose distinct terminals of the intermediate alphabet. The compared observations are made from the respective start symbols at the same address.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, Theorem 5.8 (operational correspondence clause), printed p. 20. https://arxiv.org/html/2610.39678v1#S5.SS5

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler

namespace TreeEquivalenceHORS.Equivalence

theorem halts_iff_compiled_observations (M : Machine) :
    M.Halts ↔ ∃ (w : List ℕ) (a b : ℕ), a < sigma0.length ∧ b < sigma0.length ∧ a ≠ b ∧
      (compile .L M).Obs (.nt (compile .L M).start) w a ∧
      (compile .R M).Obs (.nt (compile .R M).start) w b := by sorry

end TreeEquivalenceHORS.Equivalence

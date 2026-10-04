-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_word_program_bounds
-- name    : ResourceScheduling.Graph.word_program_bounds
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T12:37:34.111292+00:00
-- url     : https://prove2.me/theorems/4963f67d-3af6-482a-a5d2-d9ed8363f72b
-- title:
--   word program bounds
-- statement:
--   Parsing bounds the unary parameter by input length, and ordered non-edge enumeration has the stated quadratic size and index bounds.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_WordProgram
open CookPvsNP
open ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem word_program_bounds (w : List Letter) (t : ℕ) (bits : List Letter)
    (h : readUnary w = some (t, bits)) :
    t + 1 + bits.length = w.length ∧
    (wordNonEdges (3 * t) bits).length ≤ 9 * w.length ^ 2 ∧
    (∀ p ∈ wordNonEdges (3 * t) bits,
      p.1 < p.2 ∧ p.2 < 3 * t ∧ bits.getD (p.1 * (3 * t) + p.2) Letter.sep ≠ Letter.one) := by sorry
end ResourceScheduling.Graph

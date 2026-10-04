-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_word_non_edges
-- name    : ResourceScheduling.Graph.word_non_edges
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T12:37:25.09916+00:00
-- url     : https://prove2.me/theorems/80c0b2b9-7893-4d1c-bf45-2dcfa05603be
-- title:
--   word non edges
-- statement:
--   Natural-index resource enumeration agrees with the original ordered graph non-edge list.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_WordProgram
open CookPvsNP
open ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem word_non_edges (n : ℕ) (bits : List Letter) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (h : ∀ i j : Fin n, G.Adj i j ↔ bits.getD (i.val * n + j.val) Letter.sep = Letter.one) :
    wordNonEdges n bits = (nonEdgeList G).map (fun p => (p.1.val, p.2.val)) := by sorry
end ResourceScheduling.Graph

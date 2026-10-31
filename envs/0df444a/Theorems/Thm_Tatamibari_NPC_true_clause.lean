-- Prove2me | Theorems.Thm_Tatamibari_NPC_true_clause
-- name    : Tatamibari.NPC.true_clause
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:34:54.433985+00:00
-- url     : https://prove2.me/theorems/92dbb39d-a8cf-4b41-a184-79647dcfb757
-- title:
--   Lemma 3.12 — true clause
-- statement:
--   For every pair of nonnegative horizontal extension parameters and either clause orientation, any three incoming literal signals with at least one true signal give a locally solvable clause profile. In symbols, if v has length three and contains true, then the profile selected by v has a valid geometric rectangle covering. All seven satisfying patterns are included, with no bound on the extension parameters.
--
--   Differences from the source:
--   - encoding: grid cells, rectangles, geometric placements and finite profiles → natural row and column indices, half-open rectangles, finite lists with extensional cell membership, and explicit coordinate formulas; reason: represent the same finite geometric objects; shared edges remain allowed and four-corner incidence counts distinct rectangles
--   - reading: Section 2 area assignments partition a subpuzzle while optional areas may be uncovered → local solutions partition the selected proper profile; global solutions cover the whole board; reason: Section 3.1 and the profile diagrams require unselected optional cells to remain available to neighboring gadgets
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 13, Lemma 3.12

import Definitions.Def_Tatamibari_NPC_ClauseSemantics

set_option autoImplicit false

namespace Tatamibari.NPC

theorem true_clause (a b : Nat) (negative : Bool) (values : List Bool)
    (hlen : values.length = 3) (htrue : true ∈ values) :
    (clauseGadget a b negative).locallySolvable (clauseProfile a b negative values) := by sorry

end Tatamibari.NPC

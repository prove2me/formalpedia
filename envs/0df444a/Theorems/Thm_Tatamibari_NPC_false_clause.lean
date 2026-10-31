-- Prove2me | Theorems.Thm_Tatamibari_NPC_false_clause
-- name    : Tatamibari.NPC.false_clause
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:34:56.882891+00:00
-- url     : https://prove2.me/theorems/bde593d5-80b7-4ab8-9dfb-ea6c2c755a2c
-- title:
--   Corollary 3.11 — false clause
-- statement:
--   For every pair of nonnegative horizontal extension parameters, and in either vertical orientation, the clause gadget with all three incoming literal signals false has no local solution. The assertion concerns the geometric clause subpuzzle and its specified interface profile. It does not assert that every Tatamibari board is unsolvable.
--
--   Differences from the source:
--   - encoding: grid cells, rectangles, geometric placements and finite profiles → natural row and column indices, half-open rectangles, finite lists with extensional cell membership, and explicit coordinate formulas; reason: represent the same finite geometric objects; shared edges remain allowed and four-corner incidence counts distinct rectangles
--   - reading: Section 2 area assignments partition a subpuzzle while optional areas may be uncovered → local solutions partition the selected proper profile; global solutions cover the whole board; reason: Section 3.1 and the profile diagrams require unselected optional cells to remain available to neighboring gadgets
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 13, Corollary 3.11

import Definitions.Def_Tatamibari_NPC_ClauseSemantics

set_option autoImplicit false

namespace Tatamibari.NPC

theorem false_clause (a b : Nat) (negative : Bool) :
    ¬ (clauseGadget a b negative).locallySolvable
      (clauseProfile a b negative [false,false,false]) := by sorry

end Tatamibari.NPC

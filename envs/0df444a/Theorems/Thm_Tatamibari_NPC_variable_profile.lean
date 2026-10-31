-- Prove2me | Theorems.Thm_Tatamibari_NPC_variable_profile
-- name    : Tatamibari.NPC.variable_profile
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:34:54.429104+00:00
-- url     : https://prove2.me/theorems/b8d86ab9-507b-4a79-b371-114bfaa6a41a
-- title:
--   Lemma 3.9 — variable profile
-- statement:
--   Let n be any positive branch count and let P be any finite cell profile. The variable gadget is locally solvable with profile P if and only if P selects the branch interfaces so that all upward orientations agree, all downward orientations agree, and every upward orientation is opposite every downward orientation. The equivalence includes existence of proper interface masks representing P; profiles omitting mandatory cells, partially selecting an interface, or extending outside the gadget cannot satisfy the right-hand side.
--
--   Differences from the source:
--   - encoding: grid cells, rectangles, geometric placements and finite profiles → natural row and column indices, half-open rectangles, finite lists with extensional cell membership, and explicit coordinate formulas; reason: represent the same finite geometric objects; shared edges remain allowed and four-corner incidence counts distinct rectangles
--   - reading: Section 2 area assignments partition a subpuzzle while optional areas may be uncovered → local solutions partition the selected proper profile; global solutions cover the whole board; reason: Section 3.1 and the profile diagrams require unselected optional cells to remain available to neighboring gadgets
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 8, Lemma 3.9

import Definitions.Def_Tatamibari_NPC_ClauseSemantics

set_option autoImplicit false

namespace Tatamibari.NPC

theorem variable_profile (n : Nat) (hn : 0 < n) (profile : List Cell) :
    (variableGadget n).locallySolvable profile ↔
      ∃ upper lower : List Bool, upper.length = n ∧ lower.length = n ∧
        sameCells profile (variableProfile n upper lower) = true ∧
        consistentOrientations upper lower := by sorry

end Tatamibari.NPC

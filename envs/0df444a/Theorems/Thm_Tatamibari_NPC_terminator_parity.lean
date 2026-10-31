-- Prove2me | Theorems.Thm_Tatamibari_NPC_terminator_parity
-- name    : Tatamibari.NPC.terminator_parity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:34:44.636067+00:00
-- url     : https://prove2.me/theorems/2316d329-6f83-459e-ab4c-095095ad0cf1
-- title:
--   Lemma 3.5 — terminator parity
-- statement:
--   For each of the two incident wire parities, the terminator in Figure 4 has a local rectangle covering with the corresponding optional interface either wholly covered or wholly uncovered. No incoming parity is excluded.
--
--   Differences from the source:
--   - encoding: grid cells, rectangles, geometric placements and finite profiles → natural row and column indices, half-open rectangles, finite lists with extensional cell membership, and explicit coordinate formulas; reason: represent the same finite geometric objects; shared edges remain allowed and four-corner incidence counts distinct rectangles
--   - reading: Section 2 area assignments partition a subpuzzle while optional areas may be uncovered → local solutions partition the selected proper profile; global solutions cover the whole board; reason: Section 3.1 and the profile diagrams require unselected optional cells to remain available to neighboring gadgets
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 7, Lemma 3.5

import Definitions.Def_Tatamibari_NPC_ClauseSemantics

set_option autoImplicit false

namespace Tatamibari.NPC

theorem terminator_parity (down : Bool) :
    terminator.locallySolvable (terminator.profile [down]) := by sorry

end Tatamibari.NPC

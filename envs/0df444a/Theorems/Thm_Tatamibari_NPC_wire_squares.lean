-- Prove2me | Theorems.Thm_Tatamibari_NPC_wire_squares
-- name    : Tatamibari.NPC.wire_squares
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:34:52.714782+00:00
-- url     : https://prove2.me/theorems/52721bbb-4be8-435e-8d02-faa6fcb812c3
-- title:
--   Lemma 3.1 — wire squares
-- statement:
--   Let a positive-length wire occur at any offset in a valid Tatamibari board, and suppose it is safely placed: rectangles of vertical clues cannot reach the two exposed cells immediately to the right of its endpoint square clues. In every full solution, every square clue of the wire is covered by a rectangle of width 2 and height 2 lying within the wire area. This includes both endpoint clues. The ambient board belongs to the constructed-layout puzzle class of Sections 3.1 and 3.5, shared with clause completeness.
--
--   Differences from the source:
--   - encoding: grid cells, rectangles, geometric placements and finite profiles → natural row and column indices, half-open rectangles, finite lists with extensional cell membership, and explicit coordinate formulas; reason: represent the same finite geometric objects; shared edges remain allowed and four-corner incidence counts distinct rectangles
--   - encoding: the valid containing-puzzle class of Section 2 and the gadget layouts of Sections 3.1 and 3.5 → admissibleAmbient b, the same constructed-layout class used for clause completeness; reason: restores the shared ambient-puzzle convention; gadget lemmas do not range over arbitrary outside clue arrangements, while the headline language still includes every board
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 6, Lemma 3.1

import Definitions.Def_Tatamibari_NPC_ClauseSemantics

set_option autoImplicit false

namespace Tatamibari.NPC

theorem wire_squares (b : Board) (offset : Cell) (n : Nat) (hn : 0 < n)
    (hambient : admissibleAmbient b)
    (hemb : ((wire n).translate offset).embedded b) (hsafe : safelyPlaced b offset n)
    (rs : List Rectangle) (hsol : b.isSolution rs = true) :
    ∀ i < n, ∀ r ∈ rs, r.contains (translateCell offset (1,2*i+2)) = true →
      r.width = 2 ∧ r.height = 2 ∧ r.cells.all ((wire n).translate offset).area.contains = true := by sorry

end Tatamibari.NPC

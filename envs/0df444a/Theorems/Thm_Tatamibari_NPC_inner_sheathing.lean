-- Prove2me | Theorems.Thm_Tatamibari_NPC_inner_sheathing
-- name    : Tatamibari.NPC.inner_sheathing
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:34:42.206068+00:00
-- url     : https://prove2.me/theorems/a6ecdb08-f9a8-4394-b0b8-7d1a5b1e67af
-- title:
--   Lemma 3.3 — inner sheathing
-- statement:
--   For every positive-length safely placed wire in a solved Tatamibari board, there is one common square parity, and every vertical clue in each inner-sheathing column is covered by a width-1, height-2 rectangle staggered by one row relative to the square boundaries. Thus the sheathing has the opposite boundary parity, as well as the prescribed size. With rows increasing downwards, the square clues occupy even rows and sheathing clues odd rows, so their respective top-or-bottom clue positions use the same shift flag. The ambient board belongs to the constructed-layout puzzle class of Sections 3.1 and 3.5, shared with clause completeness.
--
--   Differences from the source:
--   - encoding: grid cells, rectangles, geometric placements and finite profiles → natural row and column indices, half-open rectangles, finite lists with extensional cell membership, and explicit coordinate formulas; reason: represent the same finite geometric objects; shared edges remain allowed and four-corner incidence counts distinct rectangles
--   - encoding: the valid containing-puzzle class of Section 2 and the gadget layouts of Sections 3.1 and 3.5 → admissibleAmbient b, the same constructed-layout class used for clause completeness; reason: restores the shared ambient-puzzle convention; gadget lemmas do not range over arbitrary outside clue arrangements, while the headline language still includes every board
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 7, Lemma 3.3

import Definitions.Def_Tatamibari_NPC_ClauseSemantics

set_option autoImplicit false

namespace Tatamibari.NPC

theorem inner_sheathing (b : Board) (offset : Cell) (n : Nat) (hn : 0 < n)
    (hambient : admissibleAmbient b)
    (hemb : ((wire n).translate offset).embedded b) (hsafe : safelyPlaced b offset n)
    (rs : List Rectangle) (hsol : b.isSolution rs = true) :
    ∃ down : Bool, wireHasParity offset n rs down ∧
      ∀ i < n, ∀ x ∈ [0,3],
        sheathPosition (translateCell offset (x,2*i+1)) down ∈ rs := by sorry

end Tatamibari.NPC

-- Prove2me | Theorems.Thm_Tatamibari_NPC_coupler_coverings
-- name    : Tatamibari.NPC.coupler_coverings
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:34:55.353054+00:00
-- url     : https://prove2.me/theorems/e9107e8c-5f05-4956-82ff-b1f279592d26
-- title:
--   Lemma 3.7 — coupler coverings
-- statement:
--   In a solved board containing any variable gadget with adjacent branches i and i+1, with the constituent wires safely placed, every rectangle covering the coupler's square clue is one of the two 2-by-2 placements shown in Figure 6: its clue is in the upper-left or lower-left cell. Validity is the ordinary seven-rule global solution predicate, not membership in this pair of rectangles. The ambient board belongs to the constructed-layout puzzle class of Sections 3.1 and 3.5, shared with clause completeness.
--
--   Differences from the source:
--   - encoding: grid cells, rectangles, geometric placements and finite profiles → natural row and column indices, half-open rectangles, finite lists with extensional cell membership, and explicit coordinate formulas; reason: represent the same finite geometric objects; shared edges remain allowed and four-corner incidence counts distinct rectangles
--   - encoding: the valid containing-puzzle class of Section 2 and the gadget layouts of Sections 3.1 and 3.5 → admissibleAmbient b, the same constructed-layout class used for clause completeness; reason: restores the shared ambient-puzzle convention; gadget lemmas do not range over arbitrary outside clue arrangements, while the headline language still includes every board
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 8, Lemma 3.7

import Definitions.Def_Tatamibari_NPC_ClauseSemantics

set_option autoImplicit false

namespace Tatamibari.NPC

theorem coupler_coverings (b : Board) (offset : Cell) (n : Nat) (i : Nat) (hi : i+1 < n)
    (hambient : admissibleAmbient b)
    (hemb : ((variableGadget n).translate offset).embedded b)
    (hsafe : variableWiresSafe b offset n) (rs : List Rectangle)
    (hsol : b.isSolution rs = true) :
    ∀ r ∈ rs, r.contains (translateCell offset (6*i+5,10)) = true →
      r = squarePosition (translateCell offset (6*i+5,10)) false ∨
      r = squarePosition (translateCell offset (6*i+5,10)) true := by sorry

end Tatamibari.NPC

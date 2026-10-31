-- Prove2me | Theorems.Thm_Tatamibari_NPC_variable_consistency
-- name    : Tatamibari.NPC.variable_consistency
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:34:52.363997+00:00
-- url     : https://prove2.me/theorems/df657e08-39c8-46fd-9ff9-0be632bd2654
-- title:
--   Lemma 3.8 — variable consistency
-- statement:
--   For any positive finite number of branches in a safely placed variable gadget, every full solution assigns a single common value to all branches. Equivalently, one choice of vertical shift applies to all nine square clues in every constituent wire. This agrees on upward branches and yields the corresponding opposite interface orientations on downward branches. The ambient board belongs to the constructed-layout puzzle class of Sections 3.1 and 3.5, shared with clause completeness.
--
--   Differences from the source:
--   - encoding: grid cells, rectangles, geometric placements and finite profiles → natural row and column indices, half-open rectangles, finite lists with extensional cell membership, and explicit coordinate formulas; reason: represent the same finite geometric objects; shared edges remain allowed and four-corner incidence counts distinct rectangles
--   - encoding: the valid containing-puzzle class of Section 2 and the gadget layouts of Sections 3.1 and 3.5 → admissibleAmbient b, the same constructed-layout class used for clause completeness; reason: restores the shared ambient-puzzle convention; gadget lemmas do not range over arbitrary outside clue arrangements, while the headline language still includes every board
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 8, Lemma 3.8

import Definitions.Def_Tatamibari_NPC_ClauseSemantics

set_option autoImplicit false

namespace Tatamibari.NPC

theorem variable_consistency (b : Board) (offset : Cell) (n : Nat) (hn : 0 < n)
    (hambient : admissibleAmbient b)
    (hemb : ((variableGadget n).translate offset).embedded b)
    (hsafe : variableWiresSafe b offset n) (rs : List Rectangle)
    (hsol : b.isSolution rs = true) :
    ∃ down : Bool, variableHasValue offset n rs down := by sorry

end Tatamibari.NPC

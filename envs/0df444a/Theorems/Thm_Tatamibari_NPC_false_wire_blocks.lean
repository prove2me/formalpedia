-- Prove2me | Theorems.Thm_Tatamibari_NPC_false_wire_blocks
-- name    : Tatamibari.NPC.false_wire_blocks
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:34:46.923471+00:00
-- url     : https://prove2.me/theorems/ba7fa750-5484-4066-a05c-766820d555b4
-- title:
--   Lemma 3.10 — false wire blocks
-- statement:
--   Let a,b be arbitrary nonnegative clause extension parameters, in either the positive clause or its vertical reflection. For any three-port configuration, any false port, and any local solution with that configuration, no rectangle of the corresponding horizontal enforcement clue crosses to column 5 of the clause-verification wire. The quantification treats each of the three ports separately and uses its own enforcement row and clue position.
--
--   Differences from the source:
--   - encoding: grid cells, rectangles, geometric placements and finite profiles → natural row and column indices, half-open rectangles, finite lists with extensional cell membership, and explicit coordinate formulas; reason: represent the same finite geometric objects; shared edges remain allowed and four-corner incidence counts distinct rectangles
--   - reading: Section 2 area assignments partition a subpuzzle while optional areas may be uncovered → local solutions partition the selected proper profile; global solutions cover the whole board; reason: Section 3.1 and the profile diagrams require unselected optional cells to remain available to neighboring gadgets
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 12, Lemma 3.10

import Definitions.Def_Tatamibari_NPC_ClauseSemantics

set_option autoImplicit false

namespace Tatamibari.NPC

theorem false_wire_blocks (a b : Nat) (negative : Bool) (values : List Bool)
    (hlen : values.length = 3) (port : Nat) (hp : port < 3)
    (hfalse : values.getD port false = false) (rs : List Rectangle)
    (hsol : (clauseGadget a b negative).localSolution
      (clauseProfile a b negative values) rs = true) :
    ∀ r ∈ rs, enforcementCrosses a b negative port r = false := by sorry

end Tatamibari.NPC

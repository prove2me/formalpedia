-- Prove2me | Theorems.Thm_Tatamibari_NPC_clause_profile_complete
-- name    : Tatamibari.NPC.clause_profile_complete
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:34:56.447895+00:00
-- url     : https://prove2.me/theorems/2c98eafa-e5e2-4be4-a43c-406bb3f0b196
-- title:
--   Lemma 3.14 — clause profile complete
-- statement:
--   For any extended clause gadget, either orientation, and any translation into an admissible constructed Tatamibari puzzle, no profile absent from Figure 12b–h can be induced by a full solution. Here a profile is a subset of the gadget area, as defined on page 3; it need not be proper. Equivalently, an induced union that is contained in the gadget area must equal one of the seven listed profiles. Consequently every unlisted profile, including improper profiles, is locally impossible in this ambient class. The induced union includes the entire rectangles assigned to gadget clues and is never clipped. Unions extending outside the gadget area are not profiles under the source definition.
--
--   Differences from the source:
--   - encoding: grid cells, rectangles, geometric placements and finite profiles → natural row and column indices, half-open rectangles, finite lists with extensional cell membership, and explicit coordinate formulas; reason: represent the same finite geometric objects; shared edges remain allowed and four-corner incidence counts distinct rectangles
--   - reading: Section 2 area assignments partition a subpuzzle while optional areas may be uncovered → local solutions partition the selected proper profile; global solutions cover the whole board; reason: Section 3.1 and the profile diagrams require unselected optional cells to remain available to neighboring gadgets
--   - encoding: the rectilinear drawing scaled to a sufficient grid in Sections 3.1 and 3.5 → the occurrence order and nesting determine explicit coordinates with fixed margins, spare branches, and 64-row layer spacing; reason: normalizes the harmless layout choices and avoids arbitrary coordinate magnitudes in the n+m size and time bound
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 14, Lemma 3.14

import Definitions.Def_Tatamibari_NPC_ClauseSemantics

set_option autoImplicit false

namespace Tatamibari.NPC

/-- Profiles are subsets of the gadget area, as defined on page 3.
The induced union is not clipped; out-of-area unions are not profiles. -/
theorem clause_profile_complete (a b : Nat) (negative : Bool) (offset : Cell) :
    ((clauseGadget a b negative).translate offset).complete
      ((clauseProfiles a b negative).map (List.map (translateCell offset)))
      admissibleAmbient := by sorry

end Tatamibari.NPC

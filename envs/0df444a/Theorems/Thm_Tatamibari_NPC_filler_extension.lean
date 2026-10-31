-- Prove2me | Theorems.Thm_Tatamibari_NPC_filler_extension
-- name    : Tatamibari.NPC.filler_extension
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:34:53.447997+00:00
-- url     : https://prove2.me/theorems/463e36cf-68db-467c-a710-2c74d7370d34
-- title:
--   Proposition 3.15 — filler extension
-- statement:
--   For every valid normalized planar rectilinear monotone formula drawing, suppose the constructed gadgets have compatible locally solvable profiles: the profiles are pairwise disjoint and partition the union of gadget areas. There is then a full seven-rule solution of the constructed board extending those profiles within each gadget and containing every prescribed filler rectangle. Outer-sheathing rectangles may extend outside their original gadgets and their meeting points may change during assembly.
--
--   Differences from the source:
--   - encoding: grid cells, rectangles, geometric placements and finite profiles → natural row and column indices, half-open rectangles, finite lists with extensional cell membership, and explicit coordinate formulas; reason: represent the same finite geometric objects; shared edges remain allowed and four-corner incidence counts distinct rectangles
--   - reading: Section 2 area assignments partition a subpuzzle while optional areas may be uncovered → local solutions partition the selected proper profile; global solutions cover the whole board; reason: Section 3.1 and the profile diagrams require unselected optional cells to remain available to neighboring gadgets
--   - encoding: the rectilinear drawing scaled to a sufficient grid in Sections 3.1 and 3.5 → the occurrence order and nesting determine explicit coordinates with fixed margins, spare branches, and 64-row layer spacing; reason: normalizes the harmless layout choices and avoids arbitrary coordinate magnitudes in the n+m size and time bound
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 16, Proposition 3.15

import Definitions.Def_Tatamibari_NPC_ClauseSemantics

set_option autoImplicit false

namespace Tatamibari.NPC

theorem filler_extension (d : Drawing) (hd : d.valid = true) (profiles : List (List Cell))
    (hp : profilesCompatible d.gadgets profiles) :
    ∃ rs, (reduction d).isSolution rs = true ∧ extendsProfiles d profiles rs ∧
      ∀ r ∈ d.fillerRectangles, r ∈ rs := by sorry

end Tatamibari.NPC

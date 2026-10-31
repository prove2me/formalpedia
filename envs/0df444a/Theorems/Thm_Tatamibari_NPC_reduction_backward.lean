-- Prove2me | Theorems.Thm_Tatamibari_NPC_reduction_backward
-- name    : Tatamibari.NPC.reduction_backward
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:34:56.13029+00:00
-- url     : https://prove2.me/theorems/bf07d646-4716-474d-bffe-842586f51c2b
-- title:
--   Proposition 3.18 — reduction backward
-- statement:
--   For every valid normalized planar rectilinear monotone three-occurrence formula drawing Phi, if Phi has no satisfying Boolean assignment, then the constructed board f(Phi) has no Tatamibari solution. This excludes every possible seven-rule rectangle solution, including solutions not presented by intended gadget coverings.
--
--   Differences from the source:
--   - encoding: grid cells, rectangles, geometric placements and finite profiles → natural row and column indices, half-open rectangles, finite lists with extensional cell membership, and explicit coordinate formulas; reason: represent the same finite geometric objects; shared edges remain allowed and four-corner incidence counts distinct rectangles
--   - encoding: the rectilinear drawing scaled to a sufficient grid in Sections 3.1 and 3.5 → the occurrence order and nesting determine explicit coordinates with fixed margins, spare branches, and 64-row layer spacing; reason: normalizes the harmless layout choices and avoids arbitrary coordinate magnitudes in the n+m size and time bound
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 17, Proposition 3.18

import Definitions.Def_Tatamibari_NPC_ClauseSemantics

set_option autoImplicit false

namespace Tatamibari.NPC

theorem reduction_backward (d : Drawing) (hd : d.valid = true) (hunsat : ¬ d.satisfiable) :
    ¬ (reduction d).solvable := by sorry

end Tatamibari.NPC

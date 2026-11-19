-- Prove2me | Theorems.Thm_PPSLattice_Supplement_theorem_6_9
-- name    : PPSLattice.Supplement.theorem_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T08:48:04.972776+00:00
-- url     : https://prove2.me/theorems/d4899e3b-c870-4073-aad8-b0c3739edc14
-- title:
--   Theorem 6.9 — adaptive pseudorandomness
-- statement:
--   For an efficient, correct, fully compact bit-message PPS, payload hiding implies adaptive pseudorandomness of the PSPRG in Construction 6.2, with at most one projection query and terminal admissibility $I\cap T=\varnothing$.
--
--   Differences from the source:
--   - encoding: The source uses a uniform PPT oracle experiment → Lean records query sets and the single projection flag in a fuel-bounded reactive run and scores inadmissible transcripts by an independent fair bit; reason: this preserves the printed adaptive query order and final admissibility test in a total function.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 6.9, p.48

import Mathlib
import Definitions.Def_PPSLattice_Supplement_PPSBit
import Definitions.Def_PPSLattice_Supplement_PSPRG
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- **Theorem 6.9 (Adaptive Pseudorandomness)**, Goyal--Yadugiri, STOC 2027 submission
(manuscript sha256 7f9c493f...), p.48. Payload hiding alone implies adaptive pseudorandomness of
Construction 6.2.

**Formalization Note.** The game permits arbitrary interleaving of evaluation queries with at most
one projection query and checks `I ∩ T = ∅` only at the end; it is not a selective game. -/
theorem theorem_6_9 (E : PPS)
    (hEff : E.Efficient)
    (hCorrect : PPSLattice.Supplement.PPS.BitCorrect E)
    (hCompact : PPSLattice.Supplement.PPS.BitFullyCompact E)
    (hPayload : PPSLattice.Supplement.PPS.BitPayloadHiding E) :
    (construction62 E).AdaptivelyPseudorandom := by sorry

end PPSLattice.Supplement

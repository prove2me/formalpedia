-- Prove2me | Theorems.Thm_PPSLattice_Supplement_theorem_6_3
-- name    : PPSLattice.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T08:42:33.913593+00:00
-- url     : https://prove2.me/theorems/62a701d9-46f0-4c15-b730-33e33d8ae133
-- title:
--   Theorem 6.3 — sampling indistinguishability
-- statement:
--   For an efficient, correct, fully compact bit-message PPS, mode indistinguishability and payload hiding imply sampling indistinguishability of the PSPRG in Construction 6.2.
--
--   Differences from the source:
--   - encoding: The source quantifies over uniform PPT oracle adversaries → Lean uses the published uniform reactive-machine substrate, explicit finite transcripts, and a fair-bit score for malformed runs; reason: this makes the same adaptive sampling experiment total in Lean.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 6.3, p.45

import Mathlib
import Definitions.Def_PPSLattice_Supplement_PPSBit
import Definitions.Def_PPSLattice_Supplement_PSPRG
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- **Theorem 6.3 (Sampling Indistinguishability)**, Goyal--Yadugiri, STOC 2027 submission
(manuscript sha256 7f9c493f...), p.45. Mode indistinguishability and payload hiding of the
bit-message PPS imply sampling indistinguishability of Construction 6.2.

**Formalization Note.** The output length and the projected set are chosen adaptively by a uniform
PPT adversary; malformed sets score an independent fair guess. -/
theorem theorem_6_3 (E : PPS)
    (hEff : E.Efficient)
    (hCorrect : PPSLattice.Supplement.PPS.BitCorrect E)
    (hCompact : PPSLattice.Supplement.PPS.BitFullyCompact E)
    (hMode : PPSLattice.Supplement.PPS.BitModeInd E)
    (hPayload : PPSLattice.Supplement.PPS.BitPayloadHiding E) :
    (construction62 E).SamplingIndistinguishable := by sorry

end PPSLattice.Supplement

-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_padded_explicit
-- name    : ReadOnceParityBP.LowerBound.padded_explicit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:29:04.508202+00:00
-- url     : https://prove2.me/theorems/7c8312b1-c4c3-49be-99de-aad5931acf16
-- title:
--   Theorem 1.2 — uniform explicitness after padding
-- statement:
--   Assume one polynomial-time Turing machine computes the exact countInput function on all Boolean lists. Then the family paddedFamily is uniformly explicit:
--
--   $$\operatorname{Explicit}(\operatorname{paddedFamily}).$$
--
--   At length N≥4 it uses n=2⌊N/4⌋ and the first 2n bits, with at most three ignored bits; shorter lengths return false. This supporting implication isolates the composition, parity extraction, and input conversion obligations from the definition layer.
--
--   Differences from the source:
--   - encoding: one polynomial-time explicit family supplied by the matching construction → the specified padded family and an implication from the exact-count machine assertion; reason: this records the concrete all-length witness and a proof step, without assuming explicitness in the goal
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Theorem 1.2 p.2, using Theorem 3.2 pp.9–10 and the parity observation p.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_Explicit

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Theorem 1.2's explicitness from Theorem 3.2: parity extraction and
padding preserve one uniform polynomial Turing-step bound. -/
theorem padded_explicit
    (hcount : Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      Computability.encodingNatBool.encode countInput)) :
    Explicit paddedFamily := by sorry

end ReadOnceParityBP.LowerBound

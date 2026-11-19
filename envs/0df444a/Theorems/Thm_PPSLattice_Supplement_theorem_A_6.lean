-- Prove2me | Theorems.Thm_PPSLattice_Supplement_theorem_A_6
-- name    : PPSLattice.Supplement.theorem_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T09:16:39.515247+00:00
-- url     : https://prove2.me/theorems/bdfd1055-5090-4adf-a1d6-98aade8d7be0
-- title:
--   Theorem A.6 — bounded adaptive robustness of Construction A.5
-- statement:
--   If a PPS over the Appendix-A field-message space is efficient, correct, fully compact, and payload hiding against ciphertext queries made after the set key is returned, then Construction A.5 exists with its exact instance count, threshold, field width, compactness, locality, and bounded adaptive robustness.
--
--   Differences from the source:
--   - encoding: The paper names Construction A.5 and Shamir sharing over $\mathbb F_{2^h}$ directly → Lean defines the exact $Q R$-instance algorithms over $h$-bit field-element encodings and packages a polynomial-time Shamir interface with correctness and perfect privacy, together with the construction's correctness, compactness, linear-size, and random-access locality certificates; reason: this ties the existential witness to Construction A.5 rather than permitting an unrelated robust PPS.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem A.6, p.68

import Mathlib
import Definitions.Def_PPSLattice_Supplement_QBoundedRPPS
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- **Theorem A.6**, Goyal--Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f...),
p.68. A PPS over the field of size `2^⌈log₂(R+1)⌉`, with
`R=λ²(λ+1)²`, that remains payload hiding against ciphertext queries after the set key is
returned yields Construction A.5, a Q-bounded robust PPS satisfying bounded adaptive robustness.

**Formalization Note.** `ConstructionA5` records the `Q·R` PPS instances, threshold `λ+1`, exact
field width, compactness, and locality. The security game permits arbitrarily interleaved encryption
and key queries and counts at most `Q` key queries. -/
theorem theorem_A_6 (E : PPS)
    (hE : PPSLattice.Supplement.PPS.IsSchemeForPostKey E AppendixFieldMessage) :
    ∃ C : ConstructionA5 E,
      PPSLattice.Supplement.QBoundedRPPS.BoundedAdaptiveRobust C.scheme
        AppendixFieldMessage := by sorry

end PPSLattice.Supplement

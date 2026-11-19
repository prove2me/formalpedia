-- Prove2me | Theorems.Thm_PPSLattice_Supplement_theorem_5_4
-- name    : PPSLattice.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T08:33:48.988096+00:00
-- url     : https://prove2.me/theorems/16b1b903-b1bb-49a3-8919-6f31e8c74111
-- title:
--   Theorem 5.4 — adaptive FBE compiler and exact overhead
-- statement:
--   If the input FBE satisfies the complete semi-static security property and the input PPS is a bit-message PPS scheme, then Construction 5.3 satisfies the complete adaptive FBE property. Its component layout gives the exact ciphertext, CRS, public-key, and secret-key accounting stated on page 34.
--
--   Differences from the source:
--   - generalization: The displayed Theorem 5.4 concludes adaptive FBE security → Lean also conjoins the exact component accounting from the immediately preceding page-34 compactness analysis; reason: projecting the first conjunct recovers Theorem 5.4, while the supplement plan explicitly retains informal Theorem 1.2's overhead.
--   - encoding: The source presents oracle games and concatenated objects informally → Lean represents them by uniform reactive machines, finite fuel, Boolean strings, tuple encodings, and explicit support-wise component layouts; reason: these are executable encodings of the same experiments and objects.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 5.4 and parameter display, p.34

import Mathlib
import Definitions.Def_PPSLattice_Supplement_Construction53
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- **Theorem 5.4**, Goyal--Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and
Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript
sha256 7f9c493f...), p.34: the two-key compiler of Construction 5.3 upgrades a semi-statically
secure FBE and a bit-message PPS to an adaptively secure FBE. Its component layout gives exactly
`2|fbe.ct|+|pps.sk_S|`, `|fbe.crs|+|pps.crs|`, `2|fbe.pk|+λ+|pps.ct|`, and
`1+|fbe.sk|`; hence every parameter grows by at most a factor two plus `poly(λ)`.

**Formalization Note.** FBE adversaries are uniform reactive machines. Handles are one-based,
corruption removes the key, and a challenge is admissible only for distinct live handles. PPS tags
are `λ`-bit strings bijectively encoded as the indices `1,...,2^λ`. -/
theorem theorem_5_4 (SSFBE : FBE) (E : PPS)
    (hFBE : SSFBE.SemiStaticSecure)
    (hPPS : PPSBit E) :
    (Construction53 SSFBE E).AdaptivelySecure ∧
      Construction53ParameterAccounting SSFBE E := by sorry

end PPSLattice.Supplement

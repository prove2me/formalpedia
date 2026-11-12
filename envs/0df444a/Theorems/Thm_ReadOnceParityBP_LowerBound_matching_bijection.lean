-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_matching_bijection
-- name    : ReadOnceParityBP.LowerBound.matching_bijection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:27:42.927522+00:00
-- url     : https://prove2.me/theorems/812843a9-7fcb-4720-9eb4-ef0710a7b2e5
-- title:
--   Definition 2.3 — canonical matching is a bijection
-- statement:
--   Let n be even and B⊆{0,…,n−1} have cardinality n/2. The actual canonical deletion map is a bijection:
--
--   $$\sigma_B:B\overset{\sim}{\longrightarrow}\{0,\ldots,n-1\}\setminus B.$$
--
--   The assertion verifies the construction used by every polynomial and counting item. It is not an arbitrary matching supplied as data.
--
--   Differences from the source:
--   - encoding: cycle positions Zₙ and two n-variable blocks → Fin n for the positions and Fin n ⊕ Fin n for the variables; reason: this retains exactly 2n distinct variables and the ordinary representative order for positive even n
--   - generalization: positive even cycle lengths → also the empty cycle n=0; reason: the unique half-subset is empty; its empty matching makes the geometric clauses vacuous and its polynomial and exact count equal one
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Definition 2.3, p.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_CanonicalMatching

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Definition 2.3: the deletion construction produces a genuine bijection. -/
theorem matching_bijection (n : ℕ) (hn : Even n) (B : Finset (Fin n))
    (hB : B.card = n / 2) :
    Set.BijOn (sigma B) (B : Set (Fin n)) ((B : Set (Fin n))ᶜ) := by sorry

end ReadOnceParityBP.LowerBound

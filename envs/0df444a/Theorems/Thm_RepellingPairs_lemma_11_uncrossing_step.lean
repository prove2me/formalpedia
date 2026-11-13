-- Prove2me | Theorems.Thm_RepellingPairs_lemma_11_uncrossing_step
-- name    : RepellingPairs.lemma_11_uncrossing_step
-- status  : Proved
-- author  : @iris
-- created : 2026-11-07T11:04:12.887572+00:00
-- url     : https://prove2.me/theorems/0838d241-4b33-40bd-9944-3e7650eac19b
-- title:
--   Lemma 11 — an uncrossing that preserves dominance
-- statement:
--   Let $C,C'$ be perfect matchings on $n$ points of a circle with $C\succ C'$. Then $C$ contains a pair of chords that cross, such that the configuration obtained by uncrossing these chords still dominates $C'$.
--
--   Iterating this gives Lemma 10 in the case where chords do not share endpoints.
--
--   Differences from the source:
--   - encoding: configurations whose chords give a perfect matching on all points → a fixed-point-free involution with its configuration; reason: the same object; the partner function is the page's C(x)
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), Lemma 11, p.11

import Mathlib
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_PerfectMatching
import Definitions.Def_RepellingPairs_IsGoodPair

set_option autoImplicit false

namespace RepellingPairs

/-- **Lemma 11.** If perfect matchings satisfy `C ≻ C′`, then `C` contains a pair of chords that cross, such that the
configuration obtained by uncrossing them still dominates `C′`. Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version
of October 23, 2026), Lemma 11, p.11. -/
theorem lemma_11_uncrossing_step {n : ℕ} (C C' : PerfectMatching n)
    (h : Config.StrictlyDominates C.config C'.config) :
    ∃ C₁ : Config n, Config.UncrossStep C.config C₁ ∧ Config.Dominates C₁ C'.config := by sorry

end RepellingPairs

-- Prove2me | Theorems.Thm_SeedRecyclingDL_Codes_lemma_4_1
-- name    : SeedRecyclingDL.Codes.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:57.680861+00:00
-- url     : https://prove2.me/theorems/c11b3bd6-40d8-4750-9292-5170afc47160
-- title:
--   Lemma 4.1 — Projection at a fixed boundary
-- statement:
--   For binary payloads $x,x'$ of the same length $m$ and suffixes $s,s'$ of the same length $N$, unrestricted Damerau–Levenshtein distance satisfies
--   $$\max\{d_{\rm DL}(x,x'),d_{\rm DL}(s,s')\}\le d_{\rm DL}(x\Vert s,x'\Vert s').$$
--   The statement includes cross-boundary adjacent transpositions and all intermediate lengths. This is the projection fact needed for the suffix relation; it is not a bound on the sum of the two distances.
--
--   Differences from the source:
--   - encoding: binary strings and one-based positions → lists of Fin 2 with length predicates and current-word zero-based positions; reason: the order-preserving representation includes empty intermediate words and every unrestricted DL script
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Lemma 4.1, printed p. 11 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_Execution

set_option autoImplicit false

namespace SeedRecyclingDL.Codes

theorem lemma_4_1 (m N : ℕ) (x x' s s' : Word)
    (hx : x.length = m) (hx' : x'.length = m)
    (hs : s.length = N) (hs' : s'.length = N) :
    max (distance x x') (distance s s') ≤ distance (x ++ s) (x' ++ s') := by sorry

end SeedRecyclingDL.Codes

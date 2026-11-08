-- Prove2me | Theorems.Thm_QuadraticRE_lemma_4_10
-- name    : QuadraticRE.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:16:25.586871+00:00
-- url     : https://prove2.me/theorems/b532495b-3e69-4912-9996-ce29aa04b7a5
-- title:
--   Lemma 4.10 — $p_{4+s}\le\frac125^{-2^s}$ and $q^*_{4+s}\le\frac1420^{-2^s}$
-- statement:
--   For every integer $s\ge0$,
--   $$p_{4+s}\le\tfrac12\,5^{-2^s},\qquad q^*_{4+s}\le\tfrac14\,20^{-2^s},$$
--   for the probabilities $p_j$, $q^*_j$ defined in (8).
--
--   These doubly exponential bounds give the privacy of the encoding at depth $j\ge4$.
--
--   Differences from the source:
--   - encoding: 5^{−2^s}, 20^{−2^s} → (1/5)^(2^s), (1/20)^(2^s); reason: Lean notation; same numbers
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Lemma 4.10, p.28

import Mathlib
import Definitions.Def_QuadraticRE_pj

namespace QuadraticRE

/-- Lemma 4.10 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.28: `p_{4+s} ≤ ½ 5^{−2^s}` and `q*_{4+s} ≤ ¼ 20^{−2^s}`, for the probabilities
defined in (8). -/
theorem lemma_4_10 (s : ℕ) :
    pj (4 + s) ≤ (1 / 2) * (1 / 5 : ℝ) ^ (2 ^ s) ∧
    qStar (4 + s) ≤ (1 / 4) * (1 / 20 : ℝ) ^ (2 ^ s) := by sorry

end QuadraticRE

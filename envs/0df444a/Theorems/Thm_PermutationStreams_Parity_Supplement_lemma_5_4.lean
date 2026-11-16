-- Prove2me | Theorems.Thm_PermutationStreams_Parity_Supplement_lemma_5_4
-- name    : PermutationStreams.Parity.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:56:07.794597+00:00
-- url     : https://prove2.me/theorems/9105d4b8-7417-46d5-91ba-015e0442129c
-- title:
--   Lemma 5.4 — 231-avoidance via run bottoms and $U = W$
-- statement:
--   Let $\pi\in S_n$ have maximal contiguous decreasing runs $R_1,\dots,R_k$ (left to right) with bottoms $b_1,\dots,b_k$, and let $U(\pi)=\sum_{r}\sum_{h\in R_r}T(h-b_r)$ and $W(\pi)$ be the weighted inversion number. Then $\pi$ avoids $231$ if and only if
--
--   $$
--   b_1<b_2<\cdots<b_k\qquad\text{and}\qquad U(\pi)=W(\pi).
--   $$
--
--   This characterization is what lets $231$ be detected with a constant number of logarithmic registers: run bottoms are compared on the fly and $U$, $W$ are accumulated.
--
--   Differences from the source:
--   - encoding: positions and values in [n] = {1,…,n}, π ∈ S_n → Equiv.Perm (Fin n), with position i and value π i read as i + 1 and π i + 1; reason: every formula is evaluated on the shifted 1-based values; same instances
--   - encoding: b_1 < b_2 < ⋯ < b_k over the runs in order → π j < π j' for all run-end positions j < j'; reason: a run is identified with its last position and its bottom is the value there; a chain of strict inequalities is equivalent to the pairwise statement by transitivity
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §5.3 p. 11, Lemma 5.4

import Definitions.Def_PermutationStreams_Parity_Supplement_Patterns
import Definitions.Def_PermutationStreams_Parity_Supplement_Statistics

namespace PermutationStreams.Parity.Supplement

open PatternRangeCounting1593.RangeCounting

/-- Braverman–Zamir, STOC 2027 submission #74, Lemma 5.4, p.11. A permutation `π` of `[n]` avoids
`231` if and only if its decreasing-run bottoms increase, `b₁ < b₂ < ⋯ < b_k` (stated for every
pair of run ends in position order, equivalent by transitivity), and `U(π) = W(π)`. -/
theorem lemma_5_4 (n : ℕ) (π : Equiv.Perm (Fin n)) :
    Avoids pat231 π ↔
      ((∀ j j' : Fin n, IsRunEnd π j → IsRunEnd π j' → j < j' → π j < π j') ∧ U π = W π) := by sorry

end PermutationStreams.Parity.Supplement

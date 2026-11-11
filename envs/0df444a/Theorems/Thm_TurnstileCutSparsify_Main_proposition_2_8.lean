-- Prove2me | Theorems.Thm_TurnstileCutSparsify_Main_proposition_2_8
-- name    : TurnstileCutSparsify.Main.proposition_2_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:41:42.347419+00:00
-- url     : https://prove2.me/theorems/2016fdc9-3371-4844-b429-8b28494d5963
-- title:
--   Proposition 2.8 — a locally computable pseudorandom generator for space-bounded computation ([KMM+20, Theorem 4.1])
-- statement:
--   For any constants $q,c>0$ and every $S\ge2$, there is an explicit generator that stretches a seed of $O(S\,\mathrm{polylog}\,S)$ random bits into $S^q$ bits with the following property. If a randomized algorithm runs in space $S$ ($S$ bits of working memory, read-only access to its input, random bits read once in a fixed order) and reads at most $S^q$ random bits, then replacing these bits by the output of the generator on a uniformly random seed increases its failure probability by at most $S^{-c}$. Each output bit can be computed from the seed in $O(\log^{O(q)}S)$ time.
--
--   Differences from the source:
--   - reading: an algorithm running in space S that reads its random bits once, in a fixed order → a read-once branching program ROBP (2^S) L (L ≤ ⌊S^q⌋) over its random bits, with a failing set of final states; reason: for a fixed input such an algorithm is such a program (p. 12); fooling every program of width 2^S covers every algorithm
--   - encoding: seed of O(S polylog S) bits; S^q output bits; O(log^{O(q)} S) time per bit → s ≤ C S (log₂ S)^a; output length ⌊S^q⌋; ∃ K absolute ∀ q c ∃ C a: time ≤ C (log₂ S)^{K q}; reason: the constants of O(·) depend on q, c; the exponent O(q) has an absolute constant
--   - generalization: "explicit generator"; output bits computable in the stated time → one word-RAM program Pbit (depending on q, c only) computes every output bit for every S ≥ 2 and every word size w ≥ Cw log₂ S, given the index and the seed packed w bits per word (BitLocal); reason: a uniform program for all word sizes is in particular an explicit local computation at Θ(log S)-bit words
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), Proposition 2.8, p. 12

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileCutSparsify_Main_Streaming
import Definitions.Def_TurnstileCutSparsify_Main_Randomness

open scoped BigOperators Classical
open TurnstileRank.TightBounds.RAM

namespace TurnstileCutSparsify.Main

/-- **Proposition 2.8** ([KMM+20, Theorem 4.1]; Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), p. 12).
For any constants `q, c > 0` and every `S ≥ 2`, there is an explicit generator that stretches a seed
of `O(S polylog S)` random bits into `S^q` bits with the following property. If a randomized
algorithm runs in space `S` (`S` bits of working memory, read-only input, random bits read once in
a fixed order: a read-once branching program of width `2^S`) and reads at most `S^q` random bits,
then replacing these bits by the output of the generator on a uniformly random seed increases its
failure probability by at most `S^{−c}`. Each output bit can be computed from the seed in
`O(log^{O(q)} S)` time (on the word RAM with words of `Θ(log S)` bits, by one program). -/
theorem proposition_2_8 :
    ∃ K : ℝ, ∀ q c : ℝ, 0 < q → 0 < c →
    ∃ (C Cw : ℝ) (a : ℕ) (Pbit : Program), ∀ S : ℕ, 2 ≤ S →
    ∃ (s : ℕ) (G : (Fin s → Bool) → Fin ⌊(S : ℝ) ^ q⌋₊ → Bool),
      (s : ℝ) ≤ C * S * Real.logb 2 S ^ a ∧
      FoolsSpace S G ((S : ℝ) ^ (-c)) ∧
      ∀ w : ℕ, Cw * Real.logb 2 S ≤ w →
        ∃ cells T : ℕ, (T : ℝ) ≤ C * Real.logb 2 S ^ (K * q) ∧ BitLocal Pbit w cells T G := by sorry

end TurnstileCutSparsify.Main

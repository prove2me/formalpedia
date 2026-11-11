-- Prove2me | Theorems.Thm_TurnstileCutSparsify_Main_lemma_7_3
-- name    : TurnstileCutSparsify.Main.lemma_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:42:46.277985+00:00
-- url     : https://prove2.me/theorems/63590197-b688-41f3-acf1-cd1ff9337066
-- title:
--   Lemma 7.3 — recovery with given accurate query cuts: the accuracy-1/64 sketch of x gives a (1 ± 1/64)-cut sparsifier of x w.p. ≥ 1 − δ′, in Õ(n) bits and Õ(n) recovery time
-- statement:
--   Let $x\in\{0,1,\dots,U'\}^N$ and $0<\delta'<1/4$, with $U',\delta'^{-1}\le n^{O(1)}$. Consider the three-table sketch of $x$, built with $(U',1/64,\delta')$ in place of $(U,\varepsilon,\delta)$ and with the random tapes of Section 7.4, and its recovery with candidate discovery. Suppose that the query cuts are induced by a rooted forest with $O(\log n)$-bit weights, are accurate for $x$, and are independent of the sketch. Then the sketch uses $\tilde O(n)$ bits, and recovery takes $\tilde O(n)$ time and returns $\tilde O(n)$ edges. With probability at least $1-\delta'$, the output is a positive reweighting of pairs in $\{e:x_e>0\}$ that is a $(1\pm1/64)$-cut sparsifier of $x$.
--
--   Differences from the source:
--   - reading: "with the constants in (4)": sufficiently large absolute constants C_B and C_R, and then C_β (p. 12) → ∃ CB₀ CR₀, ∀ CB ≥ CB₀, ∀ CR ≥ CR₀, ∃ Cβ₀, ∀ Cβ ≥ Cβ₀, stated before n, U, ε, δ, w and the forest; reason: the order of choice on p. 12; the constants never depend on n, U, ε, δ or the input
--   - reading: "with the random tapes of Section 7.4" (survival and evaluation bits generated from short seeds by the generator of Proposition 2.8) → ∃ seed lengths s₁, s₂ and tape maps tξ, tσ from seeds to survival bits and evaluation signs (their total length s₁ + s₂ ≤ C n (log₂ n)^a; the seeds are part of CopySeeds and the uniform probability is over them); hashes and four-wise signs are the Appendix A.4 families (a4Hash, a4Sign: lowest bits); reason: Proposition 2.8 gives the generator only existentially, so the tapes are some short-seed tapes; their seeds count in the Õ(n) bits and their bits are computed inside the Õ(n) recovery time
--   - encoding: "the sketch uses Õ(n) bits, and recovery takes Õ(n) time and returns Õ(n) edges" → ∃ word size w (log₂ n ≤ w ≤ C log₂ n), S cells with S·w ≤ C n (log₂ n)^a, an encoding enc of (seeds, tables) into memory whose every cell is a w-bit word (< 2^w), and one recovery program Prec (chosen before n) which, with the forest written as 3n words, halts within T ≤ C n (log₂ n)^a steps on every seed, x and forest with an output of ≤ C n (log₂ n)^a entries that is the decoder's result (OutputMatches: the empty list on abort); reason: the memory holds exactly what recovery reads; S·w also counts the recovery workspace; a uniform program is stronger
--   - encoding: query cuts induced by a rooted forest with O(log n)-bit weights, ties broken deterministically → RatForest with num, den ≤ n^c and den > 0, acyclic; the implementation's path-edge choice q (∃ q valid, fixed per forest before seeds and x); accuracy assumed for (forest, q); reason: the forest and its tie-breaking are fixed before the sketch's randomness ("independent of the sketch")
--   - encoding: "a positive reweighting of pairs in {e : x_e > 0} that is a (1 ± 1/64)-cut sparsifier of x" → copyResult = some H ∧ IsPosReweighting (toR x) H ∧ IsCutSparsifier (1/64) (toR x) H; reason: same claim
--   - encoding: layers 0, …, J; rows, repetitions and groups in [R]; diagnostic copies i ∈ {1, 2}; Rademacher signs ±1 → layers k : ℕ with k ≤ J; rows, repetitions, groups in Fin R (0-based); copies in Fin 2; survival coins ξ_{e,a}, a ∈ Fin J; a sign is a bit (true = −1, sgnB); reason: re-indexing only
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), Lemma 7.3, p. 32

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileCutSparsify_Main_Streaming
import Definitions.Def_TurnstileCutSparsify_Main_Forest
import Definitions.Def_TurnstileCutSparsify_Main_Randomness
import Definitions.Def_TurnstileCutSparsify_Main_Sketch

open scoped BigOperators Classical
open TurnstileRank.TightBounds.RAM

namespace TurnstileCutSparsify.Main

/-- **Lemma 7.3** (Recovery with given query cuts; Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), p. 32).
Let `x ∈ {0, 1, …, U′}^N` and `0 < δ′ < 1/4` with `U′, δ′⁻¹ ≤ n^{O(1)}`. Consider the three-table
sketch of `x`, built with `(U′, 1/64, δ′)` in place of `(U, ε, δ)`, with the Appendix A.4 four-wise
families and the random tapes of Section 7.4 (survival and evaluation bits computed from short
seeds), and its recovery with candidate discovery. Suppose that the query cuts are induced by a
rooted forest with `O(log n)`-bit weights, are accurate for `x`, and are independent of the sketch.
Then the sketch uses `Õ(n)` bits, recovery takes `Õ(n)` time and returns `Õ(n)` edges, and with
probability at least `1 − δ′` the output is a positive reweighting of pairs in `{e : x_e > 0}` that is
a `(1 ± 1/64)`-cut sparsifier of `x`. The tape seeds have `Õ(n)` bits and the stored memory
(seeds and tables) consists of `w`-bit words, so `S · w` bounds everything recovery reads. -/
theorem lemma_7_3 :
    ∃ CB₀ CR₀ : ℝ, ∀ CB : ℝ, CB₀ ≤ CB → ∀ CR : ℝ, CR₀ ≤ CR → ∃ Cβ₀ : ℝ, ∀ Cβ : ℝ, Cβ₀ ≤ Cβ →
    ∀ c : ℕ, ∃ (C : ℝ) (a : ℕ) (Prec : Program),
    ∀ (n U' : ℕ) (δ' : ℝ), 2 ≤ n → 1 ≤ U' → 0 < δ' → δ' < 1 / 4 →
      (U' : ℝ) ≤ (n : ℝ) ^ c → δ'⁻¹ ≤ (n : ℝ) ^ c →
    let P : SketchParams := ⟨n, U', 1 / 64, δ', CB, CR, Cβ⟩
    let m := a4m P.N P.BS
    ∃ (s₁ s₂ : ℕ) (tξ : (Fin s₁ → Bool) → SurvBits n P.J)
      (tσ : (Fin s₂ → Bool) → EvalSigns n P.J P.R) (w Scells T : ℕ)
      (enc : CopySeeds P m s₁ s₂ → Tables P P.bBS → Mem Scells),
      Real.logb 2 n ≤ w ∧ (w : ℝ) ≤ C * Real.logb 2 n ∧
      ((s₁ + s₂ : ℕ) : ℝ) ≤ C * n * Real.logb 2 n ^ a ∧
      (∀ sd tb i, enc sd tb i < 2 ^ w) ∧
      ((Scells * w : ℕ) : ℝ) ≤ C * n * Real.logb 2 n ^ a ∧
      (T : ℝ) ≤ C * n * Real.logb 2 n ^ a ∧
      ∀ RF : RatForest n, RF.toForest.IsAcyclic →
        (∀ v, 0 < RF.den v ∧ (RF.num v : ℝ) ≤ (n : ℝ) ^ c ∧ (RF.den v : ℝ) ≤ (n : ℝ) ^ c) →
        ∃ q : Pair n → Fin n, QueryChoice RF.toForest q ∧
        ∀ x : Pair n → ℕ, (∀ e, x e ≤ U') →
          let S : Setup := ⟨⟨P, P.bBS, fun e => (x e : ℤ)⟩, RF.toForest, q⟩
          (∀ sd : CopySeeds P m s₁ s₂, ∃ (mem : Mem Scells) (L : List (Pair n × ℚ)),
            runWithin w Scells Prec T
                (setInputs w (enc sd (S.copyTables tξ tσ sd)) (encRatForest RF)) = some mem ∧
              decodeGraph n mem = some L ∧ (L.length : ℝ) ≤ C * n * Real.logb 2 n ^ a ∧
              OutputMatches (S.copyResult tξ tσ sd) L) ∧
          (Accurate (toR x) RF.toForest q →
            1 - δ' ≤ prob (fun sd : CopySeeds P m s₁ s₂ => ∃ H : Pair n → ℝ,
              S.copyResult tξ tσ sd = some H ∧ IsPosReweighting (toR x) H ∧
                IsCutSparsifier (1 / 64) (toR x) H)) := by sorry

end TurnstileCutSparsify.Main

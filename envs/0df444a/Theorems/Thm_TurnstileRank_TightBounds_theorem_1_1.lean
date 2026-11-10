-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_theorem_1_1
-- name    : TurnstileRank.TightBounds.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:07:31.147593+00:00
-- url     : https://prove2.me/theorems/9fce3018-fee9-4088-8600-c31c2ae0498b
-- title:
--   Theorem 1.1 — turnstile rank estimation needs and suffices with Θ(RQ(ε, n, U)) bits
-- statement:
--   Theorem 1.1 (Main result). Let U, n, ε be parameters such that 0 < ε ≤ 1/8 and n ≥ log² U. Set L = log(2 + Uε). Rank sketches for turnstile streams of final ℓ1 norm at most n, with success probability at least 2/3 for each fixed query, have optimal space complexity RQ(ε, n, U) := Θ(min{ε⁻¹L^{3/2} log(2 + nε/√L), ε⁻² log U log n, log (U+n choose n)}) bits.
--
--   All logarithms are base two (§3.2). The upper bound is for algorithms that store their random seed (p. 11); the lower bound holds even when random bits are free (§4 preamble, §6).
--
--   In Lean: there are constants $0<c\le C$ such that for all $U\ge1$, $n\ge1$ with $(\log_2U)^2\le n$ and all $0<\varepsilon\le1/8$: (upper) there is a randomized turnstile algorithm on $[U]$ that stores its seed (`IsStoredSeed`: transitions and output ignore the seed, which only picks the initial state), is correct for $(U,n,\varepsilon)$ (`RankCorrect`: on every stream whose final vector is nonnegative with $\|f\|_1\le n$, every fixed query $x\le U$ is answered within $\varepsilon\|f\|_1$ of $R_f(x)$ with probability at least $2/3$), and has $\log_2|S|\le C\cdot RQ(\varepsilon,n,U)$; (lower) every correct randomized turnstile algorithm with a free persistent public seed has $\log_2|S|\ge c\cdot RQ(\varepsilon,n,U)$. Streams have any length and intermediate vectors are unrestricted.
--
--   Differences from the source:
--   - encoding: updates (u, Δ) adding an integer Δ → unit updates (published `BoolCSPDel` streams: insert or delete one copy); reason: an integer update is |Δ| unit updates and conversely, so the final vectors and the space complexity are the same
--   - encoding: universe [U] = {0, …, U − 1}; queries x ∈ {0, …, U} → `Fin U`; queries `x : ℕ` with `x ≤ U`; reason: same objects
--   - encoding: U, n with no stated lower bound → 1 ≤ U and 1 ≤ n; reason: the universe is nonempty and log n is undefined at n = 0
--   - encoding: Θ(min{…}) bits: "optimal space complexity RQ(ε, n, U) := Θ(…)" → absolute constants 0 < c ≤ C chosen before U, n, ε: an algorithm with log₂|S| ≤ C·RQ exists, and every correct algorithm has c·RQ ≤ log₂|S|; reason: O(·)/Ω(·) with an absolute constant uniform over all parameters, made explicit and quantified before them
--   - encoding: space of a rank sketch in bits → `CosDensity.memoryBits S` = log₂|S| of the finite state set of a `BoolCSPDel.TurnstileAlg (Fin U) Ω S (ℕ → ℝ)`; upper clause with the stored-seed restriction, lower clause with a persistent free public seed on any probability space; reason: the paper charges stored seeds in its algorithms (p. 11) and proves its lower bound for free seeds (§6, Theorem 6.1's S-bit algorithms)
--   - encoding: success probability at least 2/3 for each fixed query → `CosDensity.SucceedsWP μ (…) (2/3)`: a measurable event of probability ≥ 2/3 inside the success set, per stream and per query; reason: the published inner-probability convention; equal to the probability when the success set is measurable
--   - encoding: log (base two, §3.2) → `Real.logb 2`; reason: the paper's convention
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Theorem 1.1 (Main result), printed p. 2 (PDF 3)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_Rank

open scoped BigOperators
open MeasureTheory

namespace TurnstileRank.TightBounds

/-- Theorem 1.1 (Main result), both directions: there are absolute constants `0 < c ≤ C` such that
for all `U ≥ 1`, `n ≥ 1` with `n ≥ log₂² U` and `0 < ε ≤ 1/8`, (upper) some randomized turnstile rank
algorithm that stores its own seed is correct for `(U, n, ε)` with at most `C · RQ(ε, n, U)` bits of
state, and (lower) every correct randomized turnstile rank algorithm with a free public seed has at
least `c · RQ(ε, n, U)` bits of state. -/
theorem theorem_1_1 :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ (U n : ℕ) (ε : ℝ), 1 ≤ U → 1 ≤ n → Real.logb 2 U ^ 2 ≤ n → 0 < ε → ε ≤ 1 / 8 →
        (∃ (Ω S : Type) (_ : MeasurableSpace Ω) (_ : Fintype S) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (A : BoolCSPDel.TurnstileAlg (Fin U) Ω S (ℕ → ℝ)),
          IsStoredSeed A ∧ RankCorrect μ A n ε ∧ CosDensity.memoryBits S ≤ C * RQ ε n U) ∧
        (∀ (Ω S : Type) [MeasurableSpace Ω] [Fintype S] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (A : BoolCSPDel.TurnstileAlg (Fin U) Ω S (ℕ → ℝ)),
          RankCorrect μ A n ε → c * RQ ε n U ≤ CosDensity.memoryBits S) := by sorry

end TurnstileRank.TightBounds

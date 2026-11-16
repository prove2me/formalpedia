-- Prove2me | Theorems.Thm_SubsetConvFPRAS_Supplement_theorem_1_2
-- name    : SubsetConvFPRAS.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:48:51.017182+00:00
-- url     : https://prove2.me/theorems/dd8cc871-cb74-4291-b6e4-2af3ae260a80
-- title:
--   Theorem 1.2 — FPRAS for the number of common bases of two matroids given by independence oracles
-- statement:
--   There is a fully polynomial-time randomized approximation scheme (FPRAS) that, given independence oracles for two matroids $M,N$ on a common ground set $U$, estimates the number $|\mathcal B(M)\cap\mathcal B(N)|$ of common bases.
--
--   Precisely (Definition 1.1): there are one program $P$ of the bit machine and constants $C,d$ such that for every $n$, all matroids $M,N$ on $U=\{0,\dots,n-1\}$, every oracle answering their independence questions exactly, and every rational $0<\varepsilon\le1$, with $L$ the bit length of $(n,\varepsilon)$ and
--   $$B=C\,(1+n+L+\lceil\varepsilon^{-1}\rceil)^d,$$
--   every run halts within $B$ steps, using at most $B$ bit operations and at most $B$ oracle calls, with an output $\hat Z\ge0$; and on at least $3/4$ of the $2^B$ coin tapes
--   $$(1-\varepsilon)\,|\mathcal B(M)\cap\mathcal B(N)|\le\hat Z\le(1+\varepsilon)\,|\mathcal B(M)\cap\mathcal B(N)|.$$
--
--   This is the paper's headline result. The machine receives only $n$ and $\varepsilon$: no rank is supplied, and the two matroids may have different ranks, in which case there is no common basis and the output must be $0$ on at least $3/4$ of the tapes. The platform's `OAI.common_bases_fpras` is the variant that receives the common rank $r$ as input and assumes both ranks equal $r$.
--
--   Differences from the source:
--   - reading: "polynomial time" (Definition 1.1) in the oracle model, oracle calls of unit cost → one program of the published bit machine with at most B bit operations and at most B oracle calls, B = C(1 + n + L + ⌈ε⁻¹⌉)^d, with the program and C, d chosen before the instance; reason: bit cost is the most demanding standard model, so this is the non-weaker reading of polynomial time; oracle calls are counted separately with unit cost
--   - reading: an algorithm "in time polynomial" → every run, on every coin tape, halts within B steps; reason: worst-case time over the coins, the standard meaning of an FPRAS running time
--   - encoding: an accuracy parameter 0 < ε ≤ 1 → a rational ε with 0 < ε ≤ 1, written in binary; reason: an input of a bit machine is finite; the range is that of Definition 1.1
--   - encoding: Pr[(1−ε)Z ≤ Ẑ ≤ (1+ε)Z] ≥ 3/4 and Ẑ ≥ 0 → at least 3/4 of the 2^B coin tapes give an output in the interval, and the output is ≥ 0 on every tape; reason: a run of B steps reads at most B coins, so counting B-bit tapes is the fair-coin probability
--   - encoding: two matroids M, N on a common ground set U given by independence oracles; |B(M) ∩ B(N)| → Mathlib matroids on Fin n with ground set univ, an oracle answering exactly their independence questions on bit vectors (ExactOracles), and commonBaseCount; reason: the published machine model of OAI.CommonBasesFPRAS, used unchanged
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Theorem 1.2 and Definition 1.1, p.3

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_SubsetConvFPRAS_Supplement_CommonBasesInput

open scoped Classical
open OAI.CommonBasesFPRAS

namespace SubsetConvFPRAS.Supplement

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Theorem 1.2 (Counting Common Bases), p.3, with
Definition 1.1 (FPRAS), p.3. There is an FPRAS that, given independence oracles for two matroids `M, N` on
a common ground set `U`, estimates the number `|B(M) ∩ B(N)|` of common bases.

**Formalization Note.** The machine is the published `OAI.CommonBasesFPRAS` bit machine; one program
and the constants `C, d` of the polynomial are chosen before the instance. The input is `n` and the
rational `ε` only (`initialConfig12`): no rank is supplied, and the two matroids may have different
ranks, in which case there is no common base and the output must be `0` on at least `3/4` of the tapes.
Every run halts within `B = C(1 + n + L + ⌈ε⁻¹⌉)^d` steps, with at most `B` oracle calls and `B` bit
operations and a nonnegative output; probability is by counting the `2^B` coin tapes. -/
theorem theorem_1_2 :
    ∃ (k s : ℕ) (P : Program k s) (C d : ℕ),
      ∀ (n : ℕ) (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n) (ε : ℚ),
        M₁.E = Set.univ → M₂.E = Set.univ → ExactOracles M₁ M₂ O → 0 < ε → ε ≤ 1 →
        let B := resourceBound12 C d n ε
        let Z := commonBaseCount M₁ M₂
        (∀ bits : ℕ → Bool,
          let out := execution P O (initialConfig12 k s n ε) bits B
          out.output.isSome ∧ out.oracleCalls ≤ B ∧ out.bitOperations ≤ B ∧
          ∀ z, out.output = some z → 0 ≤ z) ∧
        (3 / 4 : ℚ) * (2 : ℚ) ^ B ≤
          (Nat.card {bits : Fin B → Bool //
            ∃ z, (execution P O (initialConfig12 k s n ε) (finiteBits bits) B).output = some z ∧
              relativeAccuracy ε Z z} : ℚ) := by sorry

end SubsetConvFPRAS.Supplement

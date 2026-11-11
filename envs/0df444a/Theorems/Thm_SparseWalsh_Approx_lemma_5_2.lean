-- Prove2me | Theorems.Thm_SparseWalsh_Approx_lemma_5_2
-- name    : SparseWalsh.Approx.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:04:24.198993+00:00
-- url     : https://prove2.me/theorems/1102b426-70cb-4ea6-a587-f9092a1a9ff9
-- title:
--   Lemma 5.2 — candidate coverage of the peeling stages: |W_R| = O(s/ε), missed mass ≤ ετ²/32 w.p. ≥ 31/32, and the query counts
-- statement:
--   Consider the peeling stages of Algorithm 3 with the parameters of Appendix D.1 and without the setup-time limit. The algorithm runs with a code family $E_D:\mathbb F_2^D\to\mathbb F_2^{P_D}$ that is injective, has $P_D\le c_0D$, and corrects every pattern of at most $\beta P_D$ errors, where $0<\beta\le1/8$. Then there is a constant $C$, depending only on $c_0$ and $\beta$, with the following property.
--
--   Take any $d\ge1$, $1\le s\le2^d$, $0<\varepsilon\le1$, either method and either output limit, and one of the two settings: the general one ($L=d$), or the degree setting with $1\le k\le d$ ($L=k\log_2(2d/k)$). Take any $f:\mathbb F_2^d\to\mathbb R$ and any support $T$ of an optimal $s$-term approximation of $f$, with $T\subseteq\{|a|\le k\}$ in the degree setting. Put $\tau^2=\sum_{a\notin T}\hat f(a)^2$, and let $W_R$ be the candidate set after the $R$ stages. Then:
--   - on every outcome, $|W_R|\le Cs/\varepsilon$;
--   - with probability at least $31/32$,
--   $$\sum_{a\in T\setminus W_R}\hat f(a)^2\le\frac{\varepsilon\tau^2}{32};$$
--   - on every outcome, the stages read $f$ only on a set of points fixed by the random choices, and their result depends on $f$ only through these values. That set has at most $C\big(Ls/\varepsilon+(s/\varepsilon)\log_2(2s/\varepsilon)\big)$ points with coding, and at most $C\big(L\log_2(2L)s/\varepsilon+(s/\varepsilon)\log_2(2s/\varepsilon)\big)$ with repetition.
--
--   This is the main step of the proof of Theorem 5.1: after peeling, the frequencies of $T$ not found carry at most an $\varepsilon/32$ fraction of the optimal error.
--
--   Differences from the source:
--
--   - encoding: O(s/ε) and the O(·) query bounds → C·s/ε and C·(row), with one C chosen after the code rate c₀ and correction fraction β (absolute constants in the paper) and before the instance; log = log₂; reason: explicit constant for each O(·)
--   - generalization: Algorithm 3's code from Lemma D.7 → any code family that is injective, has rate at most c₀ and corrects every pattern of at most βP errors; reason: the analysis uses only this interface; Lemma D.7's code is an instance
--   - generalization: the peeling stages of Algorithm 3 (run when no table exceeds 2^d buckets) → the peeling stages for every parameter value, including those where the algorithm would take the full-transform fallback; reason: the stages are defined for all parameters, and the statement specializes to the runs that use them
--   - reading: L = O(k log(2d/k)) in the degree setting; T chosen inside {|a| ≤ k} → L = k·log₂(2d/k) inside C·(…); hypothesis T ⊆ {a : |a| ≤ k} when k ≥ 1; reason: the constant of the O(·) is absorbed into C; the paper chooses T this way under the promise
--   - reading: these stages use … non-adaptive value queries → on every outcome the stages read f only on peelQueryPoints (fixed by the random choices) and their result (W_R, w_R) depends on f only through those values; the bound is on that set; reason: query points fixed before any answer is non-adaptivity; counting distinct points is at most counting table entries
--   - encoding: probability over the independent hashes, locators, shifts and estimation pairs → the uniform law randLaw on the record of all random objects; reason: the product of independent uniform laws is the uniform law on the product
-- source:
--   Attias, Bshouty, Medvedev, Srebro, Efficient Non-Adaptive Sparse Fourier Learning on the Boolean Cube and Finite Abelian Groups, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 21 (PDF p. 24), Lemma 5.2; proof pp. 44-46, App. D.4

import Mathlib
import Definitions.Def_SparseWalsh_Approx_Fourier
import Definitions.Def_SparseWalsh_Approx_Locators
import Definitions.Def_SparseWalsh_Approx_Algorithm3

open scoped BigOperators Matrix

namespace SparseWalsh.Approx

/-- **Lemma 5.2** (Candidate coverage), p. 21 (PDF p. 24). Consider the peeling stages of
Algorithm 3 (parameters of App. D.1, no setup-time limit), with a code family of rate at most `c₀`
(`P ≤ c₀D`), injective, correcting every pattern of at most `βP` errors, `0 < β ≤ 1/8`. There is a
constant `C` (depending only on `c₀` and `β`, which are absolute constants in the paper) such that
for every `1 ≤ s ≤ 2^d`, `0 < ε ≤ 1`, method, output limit, setting (`k = 0`: general, `L = d`;
`1 ≤ k ≤ d`: degree, `L = k·log₂(2d/k)`), every `f` and every support `T` of an optimal `s`-term
approximation (with `T ⊆ {|a| ≤ k}` in the degree setting), where `τ² = Σ_{a ∉ T} f̂(a)²`:
* deterministically `|W_R| ≤ C·s/ε`;
* with probability at least `31/32`, `Σ_{a ∈ T∖W_R} f̂(a)² ≤ ετ²/32`;
* the stages use at most `C·(Ls/ε + (s/ε)log₂(2s/ε))` value queries with coding, and
  `C·(L log₂(2L) s/ε + (s/ε)log₂(2s/ε))` with repetition: on every outcome the stages read `f`
  only at a set of at most that many points fixed by the random choices (non-adaptive), and their
  result `(W_R, w_R)` depends on `f` only through `f` on that set. -/
theorem lemma_5_2 :
    ∀ c₀ β : ℝ, 0 < c₀ → 0 < β → β ≤ 1 / 8 → ∃ C : ℝ, 0 < C ∧
      ∀ codes : (D : ℕ) → BinCode D,
        (∀ D : ℕ, 1 ≤ D → Function.Injective (fun msg : Cube D => (codes D).E *ᵥ msg) ∧
          ((codes D).P : ℝ) ≤ c₀ * D ∧ (codes D).Corrects β) →
      ∀ d s : ℕ, 1 ≤ d → 1 ≤ s → s ≤ 2 ^ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (meth : Method) (lim : OutLimit) (k : ℕ), (k = 0 ∨ (1 ≤ k ∧ k ≤ d)) →
      ∀ (f : Cube d → ℝ) (T : Finset (Cube d)), IsOptimalSupport s f T →
        (k ≠ 0 → ∀ a ∈ T, weight a ≤ k) →
        let L : ℝ := if k = 0 then (d : ℝ) else k * Real.logb 2 (2 * d / k)
        let Qrow : ℝ := match meth with
          | .coding => L * s / ε + s / ε * Real.logb 2 (2 * s / ε)
          | .repetition => L * Real.logb 2 (2 * L) * s / ε + s / ε * Real.logb 2 (2 * s / ε)
        (∀ ρ : Rand β d s ε k meth lim,
          ((candidates codes β d s ε k meth lim f ρ).card : ℝ) ≤ C * s / ε) ∧
        (31 / 32 : ENNReal) ≤ (randLaw β d s ε k meth lim).toOuterMeasure
          {ρ | ∑ a ∈ T \ candidates codes β d s ε k meth lim f ρ, hat f a ^ 2 ≤
            ε * tailSq f T / 32} ∧
        (∀ ρ : Rand β d s ε k meth lim,
          ((peelQueryPoints codes β d s ε k meth lim ρ).card : ℝ) ≤ C * Qrow) ∧
        (∀ (ρ : Rand β d s ε k meth lim) (f' : Cube d → ℝ),
          (∀ z ∈ peelQueryPoints codes β d s ε k meth lim ρ, f z = f' z) →
          peel codes β d s ε k meth lim f ρ (numStages s) =
            peel codes β d s ε k meth lim f' ρ (numStages s)) := by sorry

end SparseWalsh.Approx

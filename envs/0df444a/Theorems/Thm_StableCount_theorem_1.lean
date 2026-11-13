-- Prove2me | Theorems.Thm_StableCount_theorem_1
-- name    : StableCount.theorem_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:48:13.774198+00:00
-- url     : https://prove2.me/theorems/c4094bc3-5fd7-477c-a43a-0690d0dc15f3
-- title:
--   Theorem 1 — $\mathrm{SM}(n)<2.81^n$, with a bound on every instance in the numbers of stable partners
-- statement:
--   There is a sequence $h_1,h_2,\dots$ of positive numbers with $\sum_{d=1}^\infty h_d<\ln 2.81$ such that the following holds for every $n\ge 1$. Let $I$ be an instance with $n$ men and $n$ women, and let $D^m_v$ and $D^w_v$ be the numbers of stable partners of man $v$ and woman $v$, respectively. Then
--   $$
--   s(I)\le\exp\Bigg(\frac12\sum_{v=1}^n\bigg(\sum_{d=1}^{D^m_v-1}h_d+\sum_{d=1}^{D^w_v-1}h_d\bigg)\Bigg).
--   $$
--   In particular,
--   $$
--   \mathrm{SM}(n)\le\exp\Bigg(n\sum_{d=1}^{n-1}h_d\Bigg)<2.81^n.
--   $$
--   This is the main result of the paper. It improves the exponential base 3.55 of Palmer and Pálvölgyi, towards the base 2.28 of the best known lower bound. The finer first inequality depends on each person's number of stable partners.
--
--   **Formalization Note** The single sequence is chosen before $n$ and $I$. $D^m_v-1$ is subtraction in `ℕ`, which is safe since every person has a stable partner; the sum over `Icc 1 0` is empty.
--
--   Differences from the source:
--   - encoding: n men and n women, each with a strict ranking of the other set → the published StableMatching.Instance n: rank bijections on Fin n, with men and women both indexed by Fin n; reason: same instances
--   - encoding: a sequence h₁, h₂, … → h : ℕ → ℝ, with h 0 never read; reason: Lean convention; same sequences
--   - encoding: ∑_{d≥1} h_d is finite, or is below ln 2.81 with positive terms → Summable (d ↦ h (d+1)) together with the value of ∑' d, h (d+1); reason: tsum is 0 for a non-summable family, so the sum clause alone would say nothing; a series of positive terms below a bound converges
--   - encoding: SM(n), the maximum of s(I) → sSup of the range of numStable in ℕ; reason: the set is nonempty and bounded by n!, so the supremum is the maximum
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Theorem 1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_StableCount_Count

namespace StableCount

open StableMatching

/-- Theorem 1 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Theorem 1, p.2). There is a sequence `h₁, h₂, …` of positive numbers with
`∑_{d=1}^∞ h_d < ln 2.81` such that the following holds. Let `I` be an instance with `n` men and `n` women,
and let `Dᵐ_v` and `Dʷ_v` be the numbers of stable partners of man `v` and woman `v`. Then
`s(I) ≤ exp(½ ∑_{v=1}^n (∑_{d=1}^{Dᵐ_v−1} h_d + ∑_{d=1}^{Dʷ_v−1} h_d))`, and in particular
`SM(n) ≤ exp(n ∑_{d=1}^{n−1} h_d) < 2.81ⁿ`.

**Formalization Note** The sequence is chosen before `n` and `I`. `Summable` is stated, since `tsum` is `0`
otherwise. The indices start at `1`: `h 0` is not read. `n ≥ 1` is the paper's convention for an instance, and
the strict bound fails at `n = 0`. `Dᵐ_v − 1` is subtraction in `ℕ`, which is safe since every person has a
stable partner. -/
theorem theorem_1 :
    ∃ h : ℕ → ℝ, (∀ d, 1 ≤ d → 0 < h d) ∧ Summable (fun d => h (d + 1)) ∧
      ∑' d, h (d + 1) < Real.log 2.81 ∧
      ∀ n : ℕ, 1 ≤ n →
        (∀ I : Instance n,
          (numStable I : ℝ) ≤ Real.exp ((1 / 2) * ∑ v : Fin n,
            (∑ d ∈ Finset.Icc 1 (Dm I v - 1), h d + ∑ d ∈ Finset.Icc 1 (Dw I v - 1), h d))) ∧
        (SM n : ℝ) ≤ Real.exp ((n : ℝ) * ∑ d ∈ Finset.Icc 1 (n - 1), h d) ∧
        Real.exp ((n : ℝ) * ∑ d ∈ Finset.Icc 1 (n - 1), h d) < 2.81 ^ n := by sorry

end StableCount

-- Prove2me | Theorems.Thm_SolomonRWRE_Recurrence_lemma_1_1_ii
-- name    : SolomonRWRE.Recurrence.lemma_1_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:36.227589+00:00
-- url     : https://prove2.me/theorems/dc781cf5-bb97-4659-adee-1658554abeaa
-- title:
--   Lemma (1.1)(ii), (1.3) — for i > j, f_ij = (Σ_{n≥i} σ_j⋯σ_n)(Σ_{n≥j} σ_j⋯σ_n)⁻¹ < 1 if Σ ρ_n < ∞, and 1 otherwise
-- statement:
--   Fix an environment $(a_n)_{n\in\mathbb Z}$ with $0<a_n<1$ for all $n$, let $\sigma_n=(1-a_n)/a_n$ and $\rho_n=\sigma_1\cdots\sigma_n$ for $n\ge1$. Let $X$ be the chain in this environment started at $i$, and $f_{ij}$ the probability that it visits $j$ at some positive time. If $i>j$, then
--   $$f_{ij}=\Big(\sum_{n=i}^{\infty}\sigma_j\cdots\sigma_n\Big)\Big(\sum_{n=j}^{\infty}\sigma_j\cdots\sigma_n\Big)^{-1}<1\qquad\text{if }\sum_{n=1}^\infty\rho_n<\infty,$$
--   and
--   $$f_{ij}=1\qquad\text{if }\sum_{n=1}^\infty\rho_n=\infty .$$
--
--   This is the downward half of the hitting-probability formula; with part (i) it gives Lemma (1.5).
--
--   **Formalization Note** All sums and the quotient are taken in $[0,\infty]$; under the first hypothesis both sums are finite and positive. The sums over $n\ge i$ and $n\ge j$ are indexed by $m=n-i$ and $m=n-j$ in $\mathbb N$.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 3, Lemma (1.1)(ii), display (1.3)

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SolomonRWRE.Recurrence

/-- Solomon, *Random Walks in a Random Environment*, Ann. Probab. 3(1) (1975), p. 3,
Lemma (1.1)(ii), display (1.3): for a fixed environment with `0 < a_n < 1` for all `n` and
`i > j`, the probability `f_ij` that the chain started at `i` ever visits `j` is
`f_ij = (Σ_{n=i}^∞ σ_j ⋯ σ_n)(Σ_{n=j}^∞ σ_j ⋯ σ_n)⁻¹ < 1` if `Σ_{n=1}^∞ ρ_n < ∞`,
and `f_ij = 1` if `Σ_{n=1}^∞ ρ_n = ∞`.

**Formalization Note.** All sums are in `[0, ∞]`. The sums over `n ≥ i` (resp. `n ≥ j`) are
indexed by `m = n − i ∈ ℕ` (resp. `m = n − j`); `σ_j ⋯ σ_n` is `∏_{k ∈ [j, n]} σ_k`;
`Σ_{n=1}^∞ ρ_n` is indexed by `n + 1`. The quotient is taken in `[0, ∞]`; under the first
hypothesis both sums are finite and positive. -/
theorem lemma_1_1_ii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℤ → ℝ) (ha : ∀ n, 0 < a n ∧ a n < 1) (i j : ℤ) (hij : j < i)
    (X : ℕ → Ω → ℤ) (hX : IsChainInEnv P a i X) :
    ((∑' n : ℕ, rho a ((n : ℤ) + 1) ≠ ∞) →
      hitProb P X j =
          (∑' m : ℕ, ∏ k ∈ Finset.Icc j (i + m), sigma a k) /
            (∑' m : ℕ, ∏ k ∈ Finset.Icc j (j + m), sigma a k) ∧
        hitProb P X j < 1) ∧
    ((∑' n : ℕ, rho a ((n : ℤ) + 1) = ∞) → hitProb P X j = 1) := by sorry

end SolomonRWRE.Recurrence

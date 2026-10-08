-- Prove2me | Theorems.Thm_SolomonRWRE_Recurrence_lemma_1_1_i
-- name    : SolomonRWRE.Recurrence.lemma_1_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:38.915488+00:00
-- url     : https://prove2.me/theorems/66e9c2a5-bccd-45f2-ba35-4736af9231ba
-- title:
--   Lemma (1.1)(i), (1.2) — for i < j, f_ij = (Σ_{n≤i} 1/(σ_n⋯σ_j))(Σ_{n≤j} 1/(σ_n⋯σ_j))⁻¹ < 1 if Σ 1/ρ_{−n} < ∞, and 1 otherwise
-- statement:
--   Fix an environment $(a_n)_{n\in\mathbb Z}$ with $0<a_n<1$ for all $n$, let $\sigma_n=(1-a_n)/a_n$ and $\rho_{-n}=\sigma_{-1}\cdots\sigma_{-n}$ for $n\ge1$. Let $X$ be the chain in this environment started at $i$, and $f_{ij}$ the probability that it visits $j$ at some positive time. If $i<j$, then
--   $$f_{ij}=\Big(\sum_{n=-\infty}^{i}\frac{1}{\sigma_n\cdots\sigma_j}\Big)\Big(\sum_{n=-\infty}^{j}\frac{1}{\sigma_n\cdots\sigma_j}\Big)^{-1}<1\qquad\text{if }\sum_{n=1}^\infty\frac1{\rho_{-n}}<\infty,$$
--   and
--   $$f_{ij}=1\qquad\text{if }\sum_{n=1}^\infty\frac1{\rho_{-n}}=\infty .$$
--
--   This is the upward half of the classical hitting-probability formula for birth–death chains; together with part (ii) it decides transience or recurrence of the chain in a fixed environment (Lemma (1.5)).
--
--   **Formalization Note** All sums and the quotient are taken in $[0,\infty]$; under the first hypothesis both sums are finite and positive. The sums over $n\le i$ and $n\le j$ are indexed by $m=i-n$ and $m=j-n$ in $\mathbb N$.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, pp. 2–3, Lemma (1.1)(i), display (1.2)

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SolomonRWRE.Recurrence

/-- Solomon, *Random Walks in a Random Environment*, Ann. Probab. 3(1) (1975), pp. 2–3,
Lemma (1.1)(i), display (1.2): for a fixed environment with `0 < a_n < 1` for all `n` and
`i < j`, the probability `f_ij` that the chain started at `i` ever visits `j` is
`f_ij = (Σ_{n=−∞}^{i} 1/(σ_n ⋯ σ_j)) (Σ_{n=−∞}^{j} 1/(σ_n ⋯ σ_j))⁻¹ < 1`
if `Σ_{n=1}^∞ 1/ρ_{−n} < ∞`, and `f_ij = 1` if `Σ_{n=1}^∞ 1/ρ_{−n} = ∞`.

**Formalization Note.** All sums are in `[0, ∞]`. The sums over `n ≤ i` (resp. `n ≤ j`) are
indexed by `m = i − n ∈ ℕ` (resp. `m = j − n`); `σ_n ⋯ σ_j` is `∏_{k ∈ [n, j]} σ_k`;
`Σ_{n=1}^∞ 1/ρ_{−n}` is indexed by `n + 1`. The quotient is taken in `[0, ∞]`; under the first
hypothesis both sums are finite and positive. -/
theorem lemma_1_1_i {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℤ → ℝ) (ha : ∀ n, 0 < a n ∧ a n < 1) (i j : ℤ) (hij : i < j)
    (X : ℕ → Ω → ℤ) (hX : IsChainInEnv P a i X) :
    ((∑' n : ℕ, (rho a (-((n : ℤ) + 1)))⁻¹ ≠ ∞) →
      hitProb P X j =
          (∑' m : ℕ, (∏ k ∈ Finset.Icc (i - m) j, sigma a k)⁻¹) /
            (∑' m : ℕ, (∏ k ∈ Finset.Icc (j - m) j, sigma a k)⁻¹) ∧
        hitProb P X j < 1) ∧
    ((∑' n : ℕ, (rho a (-((n : ℤ) + 1)))⁻¹ = ∞) → hitProb P X j = 1) := by sorry

end SolomonRWRE.Recurrence

-- Prove2me | Theorems.Thm_SolomonRWRE_DiffEq_lemma_4_3
-- name    : SolomonRWRE.DiffEq.lemma_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:03.98145+00:00
-- url     : https://prove2.me/theorems/2ca02b1f-1c37-4483-a91c-72483944db23
-- title:
--   Lemma (4.2), display (4.3) — the solution of (4.1) is Z_n = Σ_{j=1}^n σ_j ⋯ σ_n
-- statement:
--   Let $\sigma_1,\sigma_2,\dots$ be real numbers (or random variables, evaluated at a fixed outcome) and let $Z_n$ solve (4.1): $Z_0=0$, $Z_n=\sigma_n(1+Z_{n-1})$. Then for every $n\ge1$
--   $$
--   Z_n=\sum_{j=1}^{n}\sigma_j\cdots\sigma_n .
--   $$
--
--   This closed form expresses $Z_n$ as a sum of products of consecutive $\sigma$'s ending at $\sigma_n$, which is the starting point for every limit result of §4.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 28, Lemma (4.2), display (4.3)

import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System

open MeasureTheory ProbabilityTheory Filter Topology

namespace SolomonRWRE.DiffEq

/-- **Lemma (4.2), display (4.3)** (Solomon, Ann. Probab. 3(1) (1975), p. 28): the solution of
(4.1) is `Z_n = Σ_{j=1}^n σ_j ⋯ σ_n` for `n ≥ 1`. Pathwise, for every real sequence. -/
theorem lemma_4_3 {Ω : Type*} (σ : ℕ → Ω → ℝ) (n : ℕ) (hn : 1 ≤ n) (ω : Ω) :
    Z σ n ω = ∑ j ∈ Finset.Icc 1 n, ∏ i ∈ Finset.Icc j n, σ i ω := by sorry

end SolomonRWRE.DiffEq

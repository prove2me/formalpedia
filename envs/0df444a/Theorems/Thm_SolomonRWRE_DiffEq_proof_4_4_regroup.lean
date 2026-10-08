-- Prove2me | Theorems.Thm_SolomonRWRE_DiffEq_proof_4_4_regroup
-- name    : SolomonRWRE.DiffEq.proof_4_4_regroup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:44.102407+00:00
-- url     : https://prove2.me/theorems/d8caa71d-85d8-4c48-856f-144799ddf8c6
-- title:
--   Proof of Theorem (4.4), p. 28 — Z_1 + ⋯ + Z_n = Y_1^n + ⋯ + Y_n^n
-- statement:
--   Let $Z_n$ solve (4.1) and let $Y_k^n=\sum_{j=1}^{n-k+1}\prod_{i=j}^{j+k-1}\sigma_i$ be the sum of the products of $k$ consecutive $\sigma$'s among $\sigma_1,\dots,\sigma_n$. Then for every $n$ and every outcome
--   $$
--   Z_1+\dots+Z_n=Y_1^n+\dots+Y_n^n .
--   $$
--
--   The identity regroups the partial sums of $Z$ by the length of the product blocks, so that each group $Y_k^n$ is a partial sum of a stationary sequence.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 28, proof of Theorem (4.4), first paragraph (unnumbered)

import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System

open MeasureTheory ProbabilityTheory Filter Topology

namespace SolomonRWRE.DiffEq

/-- **Proof of Theorem (4.4), p. 28** (unnumbered): "It is clear that
`Z_1 + ⋯ Z_n = Y_1^n + ⋯ + Y_n^n`" (the page omits a `+`). Pathwise, for every real
sequence and every `n`. -/
theorem proof_4_4_regroup {Ω : Type*} (σ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∑ m ∈ Finset.Icc 1 n, Z σ m ω = ∑ k ∈ Finset.Icc 1 n, Y σ k n ω := by sorry

end SolomonRWRE.DiffEq

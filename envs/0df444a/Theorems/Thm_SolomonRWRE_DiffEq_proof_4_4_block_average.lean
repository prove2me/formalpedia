-- Prove2me | Theorems.Thm_SolomonRWRE_DiffEq_proof_4_4_block_average
-- name    : SolomonRWRE.DiffEq.proof_4_4_block_average
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:07.614166+00:00
-- url     : https://prove2.me/theorems/e4e0ece6-a0b0-413c-a063-cc7e7e809dd9
-- title:
--   Proof of Theorem (4.4), pp. 28–29 — for fixed k ≥ 1, lim_{n→∞} Y_k^n/n = ν^k a.e.
-- statement:
--   Let $\sigma_1,\sigma_2,\dots$ be i.i.d. nonnegative random variables with mean $\nu=E(\sigma)\in[0,\infty]$, and let $Y_k^n=\sum_{j=1}^{n-k+1}\prod_{i=j}^{j+k-1}\sigma_i$. For every fixed $k\ge1$, almost surely
--   $$
--   \lim_{n\to\infty}\frac{Y_k^n}{n}=\nu^k ,
--   $$
--   the limit being taken in $[0,\infty]$ (so it is $+\infty$ when $\nu=\infty$).
--
--   Each block product $\sigma_j\cdots\sigma_{j+k-1}$ has mean $\nu^k$, and the sequence of block products, indexed by $j$, is stationary. This law of large numbers is used in both halves of Theorem (4.4).
--
--   **Formalization Note** The ratio is mapped to $[0,\infty]$ by $x\mapsto\max(x,0)$, which loses nothing since $Y_k^n\ge0$.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, pp. 28–29, proof of Theorem (4.4), first paragraph (unnumbered display)

import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System

open MeasureTheory ProbabilityTheory Filter Topology

namespace SolomonRWRE.DiffEq

/-- **Proof of Theorem (4.4), pp. 28–29** (unnumbered): for `k` fixed,
`lim_{n→∞} Y_k^n / n = ν^k` a.e.

**Formalization Note.** The limit is taken in `[0, ∞]` (via `ENNReal.ofReal`, harmless since
`Y_k^n ≥ 0`), because `ν = E(σ)` may be `∞`, and then `ν^k = ∞`. `k ≥ 1` as on the page
(the products have `k` factors). -/
theorem proof_4_4_block_average {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℕ → Ω → ℝ) (hσ : IsIIDNonneg P σ) (k : ℕ) (hk : 1 ≤ k) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ENNReal.ofReal (Y σ k n ω / n)) atTop
      (𝓝 (nu P σ ^ k)) := by sorry

end SolomonRWRE.DiffEq

-- Prove2me | Theorems.Thm_SolomonRWRE_DiffEq_proof_4_4_liminf
-- name    : SolomonRWRE.DiffEq.proof_4_4_liminf
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:55.960405+00:00
-- url     : https://prove2.me/theorems/0e84eb96-e76d-4f2e-a850-a99c098e54b3
-- title:
--   Proof of Theorem (4.4), p. 29 — lim inf (Z_1 + ⋯ + Z_n)/n ≥ Σ_{k=1}^∞ ν^k a.e. (Fatou)
-- statement:
--   Let $\sigma_1,\sigma_2,\dots$ be i.i.d. nonnegative random variables with mean $\nu=E(\sigma)\in[0,\infty]$ and let $Z_n$ solve (4.1). Then almost surely
--   $$
--   \liminf_{n\to\infty}\frac{Z_1+\dots+Z_n}{n}\ \ge\ \sum_{k=1}^{\infty}\nu^k ,
--   $$
--   in $[0,\infty]$.
--
--   When $\nu\ge1$ the right side is $+\infty$, which is the second case of Theorem (4.4); when $\nu<1$ it equals $\nu/(1-\nu)$ and gives the lower half of the first case.
--
--   **Formalization Note** No hypothesis on $\nu$ is made, as on the page. The series is written as $\sum_{k\ge0}\nu^{k+1}$ in $[0,\infty]$, and the averages are mapped to $[0,\infty]$, which loses nothing since $Z_k\ge0$.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 29, proof of Theorem (4.4), second display (unnumbered)

import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System

open MeasureTheory ProbabilityTheory Filter Topology

namespace SolomonRWRE.DiffEq

/-- **Proof of Theorem (4.4), p. 29** (unnumbered): a.e.
`lim inf_{n→∞} (Z_1 + ⋯ + Z_n)/n ≥ Σ_{k=1}^∞ ν^k` (by Fatou's lemma); this proves (4.4) when
`ν ≥ 1`.

**Formalization Note.** In `[0, ∞]`; the series `Σ_{k≥1} ν^k` is the `tsum` of `ν^(k+1)`
over `k : ℕ` (index shift), and equals `∞` when `ν ≥ 1`. No hypothesis on `ν`, as on the
page. -/
theorem proof_4_4_liminf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℕ → Ω → ℝ) (hσ : IsIIDNonneg P σ) :
    ∀ᵐ ω ∂P, ∑' k : ℕ, nu P σ ^ (k + 1) ≤
      liminf (fun n : ℕ => ENNReal.ofReal ((∑ m ∈ Finset.Icc 1 n, Z σ m ω) / n)) atTop := by sorry

end SolomonRWRE.DiffEq

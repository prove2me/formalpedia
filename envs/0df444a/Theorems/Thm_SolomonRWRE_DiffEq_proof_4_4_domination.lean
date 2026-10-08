-- Prove2me | Theorems.Thm_SolomonRWRE_DiffEq_proof_4_4_domination
-- name    : SolomonRWRE.DiffEq.proof_4_4_domination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:37:00.249982+00:00
-- url     : https://prove2.me/theorems/57674a43-f545-4cb2-b0d4-73496b7597ec
-- title:
--   Proof of Theorem (4.4), p. 29 — Z_n ≤ S_n = Σ_{j=−∞}^n σ_j ⋯ σ_n, and S_n < ∞ a.e. when ν < 1
-- statement:
--   Let $\{\sigma_j\}_{j\in\mathbb Z}$ be i.i.d. nonnegative random variables with mean $\nu=E(\sigma)\in[0,\infty]$, let $Z_n$ solve (4.1) with $\sigma_1,\dots,\sigma_n$, and let $S_n=\sum_{j=-\infty}^{n}\sigma_j\cdots\sigma_n\in[0,\infty]$. Then:
--
--   1. for every $n\ge0$ and every outcome,
--   $$
--   Z_n=\sum_{j=1}^{n}\sigma_j\cdots\sigma_n\ \le\ \sum_{j=-\infty}^{n}\sigma_j\cdots\sigma_n=S_n ;
--   $$
--   2. if $\nu<1$, then for every $n\in\mathbb Z$, $S_n<\infty$ almost surely.
--
--   The domination replaces $Z_n$, which is not stationary, by the stationary sequence $S_n$, to which the ergodic theorem applies.
--
--   **Formalization Note** This statement is about a two-sided family (`TwoSided`), the page's "without loss of generality" coordinate model, not about the one-sided sequence of Theorem (4.4). The mean $\nu$ is that of $\sigma_1$.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 29, proof of Theorem (4.4), third paragraph (unnumbered display and the parenthetical remark after it)

import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System
import Definitions.Def_SolomonRWRE_DiffEq_TwoSided

open MeasureTheory ProbabilityTheory Filter Topology

namespace SolomonRWRE.DiffEq

/-- **Proof of Theorem (4.4), p. 29** (unnumbered): for a two-sided i.i.d. nonnegative family
`{σ_j}_{j ∈ ℤ}`, `Z_n(σ) = Σ_{j=1}^n σ_j ⋯ σ_n ≤ Σ_{j=−∞}^n σ_j ⋯ σ_n = S_n(σ)`, and
"`S_n` is finite a.e. since `ν < 1`".

**Formalization Note.** This is stated for the `ℤ`-indexed family `IsIIDNonnegZ` (the page's
"without loss of generality" coordinate model), not for the `ℕ`-indexed family of the goal;
`Z` is computed from its restriction to `ℕ` (it uses `σ_1, …, σ_n` only), and
`ν = E(σ_1)` is `nu` of that restriction. The comparison is pathwise in `[0, ∞]`
(`Z_n ≥ 0` there); the finiteness is for every `n ∈ ℤ`. -/
theorem proof_4_4_domination {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℤ → Ω → ℝ) (hσ : IsIIDNonnegZ P σ) :
    (∀ (n : ℕ) (ω : Ω), ENNReal.ofReal (Z (fun m : ℕ => σ m) n ω) ≤ S σ n ω) ∧
    (nu P (fun m : ℕ => σ m) < 1 → ∀ n : ℤ, ∀ᵐ ω ∂P, S σ n ω < ⊤) := by sorry

end SolomonRWRE.DiffEq

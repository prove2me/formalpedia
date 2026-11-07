-- Prove2me | Theorems.Thm_SubsetConvFPRAS_theorem_1_6
-- name    : SubsetConvFPRAS.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:26.601477+00:00
-- url     : https://prove2.me/theorems/c1f7ec03-8fed-44c2-b731-14474ab3fdc1
-- title:
--   Theorem 1.6 — FPRAS for any coefficient $Z_\alpha$ of $g_\mu g_\nu$, log-concave $\mu,\nu$, in $\tilde O(n^{11}(n+\log R_\mu R_\nu)^2/\varepsilon^2)$
-- statement:
--   Let $\mu,\nu:2^U\to\mathbb R_{\ge0}$ be nonnegative weights given by value oracles, with $g_\mu,g_\nu$ log-concave, and let $n=|U|$. Assume sets $S_0,T_0\subseteq U$ with $\mu(S_0)>0$, $\nu(T_0)>0$, upper bounds $R_\mu,R_\nu$ on the coefficient ranges (2), an exponent vector $\alpha\in\{0,1,2\}^U$ and an error parameter $0<\varepsilon\le1$ are given. Then there is an FPRAS for the coefficient
--   $$Z_\alpha=[x^\alpha]\bigl(g_\mu(x)\,g_\nu(x)\bigr)$$
--   that uses at most
--   $$\tilde O\Bigl(n^{11}\,\frac{(n+\log(R_\mu R_\nu))^2}{\varepsilon^2}\Bigr)$$
--   arithmetic operations and evaluation oracle calls.
--
--   Precisely: there are one program $P$ of the arithmetic model and constants $C,K$ such that for every instance, with $\Lambda=n+1+\log(R_\mu R_\nu)$ and
--   $$B=\bigl\lceil C(n+1)^{11}\Lambda^2\varepsilon^{-2}\log^K(2+\Lambda+\varepsilon^{-1})\bigr\rceil,$$
--   every run halts within $B$ steps with an output $\hat Z\ge0$, and on at least $3/4$ of the $B$-bit coin tapes $(1-\varepsilon)Z_\alpha\le\hat Z\le(1+\varepsilon)Z_\alpha$ (Definition 1.1).
--
--   This is the paper's main algorithmic result. The case $\alpha=\mathbf 1$ with $\mu=\mathbf 1[S\in\mathcal B(M)]$, $\nu(T)=\mathbf 1[U\setminus T\in\mathcal B(N)]$ counts the common bases of two matroids (Theorem 1.2, already on the platform as `OAI.common_bases_fpras`).
--
--   **Formalization Note** Input layout: integer cell $0$ holds $n$, cell $1+u$ holds $\alpha_u$; bitmaps $0,1$ hold $S_0,T_0$; real cells $0,1,2$ hold $\varepsilon,R_\mu,R_\nu$. The weights need not be homogeneous, $\alpha$ is arbitrary, and $Z_\alpha=0$ is allowed (then the output must be $0$ on $3/4$ of the tapes).
--
--   Differences from the source:
--   - reading: an unnamed randomness primitive ("chooses with probability p") → fair coins only, one tape bit per coin instruction; reason: the page names no primitive for its arithmetic model; a unit-cost uniform real would be a stronger machine and so a weaker theorem
--   - encoding: an algorithm in the arithmetic model, O(·) operations and oracle calls → one admissible program of the unit-cost real RAM, with the constant C chosen before the instance and work counted per executed instruction; reason: the paper's model (p.44); every instruction costs 1, which only adds to the count
--   - reading: "uses at most" Õ(·) operations → every run, on every coin tape, halts within the bound; reason: the proof bounds the cost on every execution (Theorem 5.1, p.21; p.25)
--   - encoding: Õ(n¹¹(n + log(R_μR_ν))²/ε²) → C(n+1)¹¹Λ²ε⁻²·log^K(2 + Λ + ε⁻¹) with Λ = n + 1 + log(R_μR_ν), C and K chosen before the instance; reason: (n+1) and Λ are within constant factors of n and n + log(R_μR_ν) for n ≥ 1, and cover U = ∅, where n¹¹ = 0 could not bound a program that must run; the log base exceeds 1, so the polylog factor never vanishes
--   - encoding: Pr[(1−ε)Z ≤ Ẑ ≤ (1+ε)Z] ≥ 3/4 and Ẑ ≥ 0 → at least 3/4 of the B-bit tapes give an output in the interval, and the output is ≥ 0 on every tape; reason: a run of B steps reads at most B coins, so counting B-bit tapes is the fair-coin probability
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Theorem 1.6 and footnote 2, pp.4–5; Definition 1.1, p.3; Õ convention, §3.1, p.16

import Mathlib
import Definitions.Def_SubsetConvFPRAS_SetWeights
import Definitions.Def_SubsetConvFPRAS_Machine

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Theorem 1.6 (FPRAS for Log-Concave Subset Convolution), pp.4–5, with
Definition 1.1, p.3. Let `μ, ν` be nonnegative weights given by evaluation oracles with `g_μ, g_ν` log-concave, with sets
`S₀, T₀` of positive weight, upper bounds on `R_μ, R_ν`, and `0 < ε ≤ 1`. There is an FPRAS for every coefficient
`Z_α = [x^α](g_μ g_ν)`, `α ∈ {0,1,2}^U`, using at most `Õ(n¹¹ (n + log(R_μ R_ν))² / ε²)` arithmetic operations and evaluation
oracle calls.

**Formalization Note.** One program `P`, with the constants `C, K` of the `Õ`, is chosen before the instance. The input
layout is `initGoal`. The bound holds on every tape, and the output is nonnegative on every tape; probability is by counting
tapes. `(n+1)` replaces `n` to cover `U = ∅`, on which `n¹¹ = 0` could not bound a program that must run; for `n ≥ 1` it is
within `2¹¹` of `n`. The base of the polylogarithm exceeds `1`, so the bound never collapses. -/
theorem theorem_1_6 :
    ∃ (P : Program) (C K : ℕ), Admissible P ∧
      ∀ (n : ℕ) (μ ν : Finset (Fin n) → ℝ), (∀ S, 0 ≤ μ S) → (∀ S, 0 ≤ ν S) →
        IsLogConcave μ → IsLogConcave ν →
      ∀ (S₀ T₀ : Finset (Fin n)), 0 < μ S₀ → 0 < ν T₀ →
      ∀ (Rμ Rν : ℝ), RangeLE μ Rμ → RangeLE ν Rν →
      ∀ (α : Fin n → Fin 3) (ε : ℝ), 0 < ε → ε ≤ 1 →
        let Λ : ℝ := (n : ℝ) + 1 + Real.log (Rμ * Rν)
        let B : ℕ := ⌈(C : ℝ) * ((n : ℝ) + 1) ^ 11 * Λ ^ 2 * (ε⁻¹) ^ 2 *
          (Real.log (2 + Λ + ε⁻¹)) ^ K⌉₊
        let s₀ := initGoal α S₀ T₀ ε Rμ Rν
        (∀ ω : ℕ → Bool, ∃ z : ℝ,
          (run P μ ν s₀ ω B).output = some z ∧ 0 ≤ z ∧ (run P μ ν s₀ ω B).work ≤ B) ∧
        (3 / 4 : ℝ) * 2 ^ B ≤
          (tapeCount P μ ν s₀ B (fun st => ∃ z : ℝ, st.output = some z ∧
            (1 - ε) * coeffZ μ ν α ≤ z ∧ z ≤ (1 + ε) * coeffZ μ ν α) : ℝ) := by sorry

end SubsetConvFPRAS

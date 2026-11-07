-- Prove2me | Theorems.Thm_PFRelease_lemma_A_10
-- name    : PFRelease.lemma_A_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:43:49.994623+00:00
-- url     : https://prove2.me/theorems/29a425a9-73a2-4e17-a687-5bbe66e5ef3f
-- title:
--   Lemma A.10 — adapted Bernoulli sequences are dominated by binomials
-- statement:
--   Let $N\in\mathbb N$ and $p\in[0,1]$. Let $X_1,\dots,X_N$ be $\{0,1\}$-valued random variables and $\mathcal G_0\subseteq\cdots\subseteq\mathcal G_N$ $\sigma$-algebras such that $X_j$ is $\mathcal G_j$-measurable.
--
--   1. If $\Pr[X_j=1\mid\mathcal G_{j-1}]\le p$ almost surely for every $j$, then for every $y\in\mathbb R$
--   $$
--   \Pr\Big[\sum_jX_j\ge y\Big]\le\Pr[\mathrm{Bin}(N,p)\ge y].
--   $$
--   2. If $\Pr[X_j=1\mid\mathcal G_{j-1}]\ge p$ almost surely for every $j$, then for every $y\in\mathbb R$
--   $$
--   \Pr\Big[\sum_jX_j< y\Big]\le\Pr[\mathrm{Bin}(N,p)< y].
--   $$
--
--   The second item bounds the number of private calls before the $\kappa$th failure in target charging.
--
--   **Formalization Note** Indices are $0$-based: `X j` is $X_{j+1}$, measurable for `G (j+1)` and conditioned on `G j`.
--
--   Differences from the source:
--   - encoding: $\sigma$-algebras $\mathcal G_0\subseteq\cdots\subseteq\mathcal G_N$ of a probability space → a monotone family `G : Fin (N+1) → MeasurableSpace Ω` of sub-$\sigma$-algebras of the ambient one, 0-based indices; reason: conditional probabilities are taken with respect to sub-$\sigma$-algebras; same instances
--   - encoding: $\Pr[X_j=1\mid\mathcal G_{j-1}]$ → the conditional expectation of the indicator of $\{X_j=1\}$ given $\mathcal G_{j-1}$; reason: definition of conditional probability
--   - encoding: $\mathrm{Bin}(N,p)$ with $p\in[0,1]$ → `PMF.binomial p hp N` with `p : ℝ≥0`, `p ≤ 1`; reason: same law
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Lemma A.10, p.29 (PDF p.31)

import Mathlib

open MeasureTheory

namespace PFRelease

/-- **Lemma A.10 (Adapted Bernoulli sequences)** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via
Private Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Lemma A.10, p.29 = PDF p.31).
Given `N ∈ ℕ`, `p ∈ [0, 1]`, `{0, 1}`-valued random variables `X₁, …, X_N` and σ-algebras
`G₀ ⊆ ⋯ ⊆ G_N` such that `X_j` is `G_j`-measurable:
1. if `Pr[X_j = 1 | G_{j−1}] ≤ p` almost surely for every `j`, then
   `Pr[Σ_j X_j ≥ y] ≤ Pr[Bin(N, p) ≥ y]` for every `y ∈ ℝ`;
2. if `Pr[X_j = 1 | G_{j−1}] ≥ p` almost surely for every `j`, then
   `Pr[Σ_j X_j < y] ≤ Pr[Bin(N, p) < y]` for every `y ∈ ℝ`.

**Formalization Note** The variables live on a probability space `(Ω, μ)`; indices are 0-based:
`X j` (`j : Fin N`) is the paper's `X_{j+1}`, measurable for `G (j+1)`, and is conditioned on
`G j`. The σ-algebras are sub-σ-algebras of the ambient one. `Pr[X_j = 1 | G]` is the
conditional expectation of the indicator of `{X_j = 1}`. `Bin(N, p)` is `PMF.binomial` on
`{0, …, N}`. -/
theorem lemma_A_10 {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (p : NNReal) (hp : p ≤ 1) (X : Fin N → Ω → ℝ)
    (hX01 : ∀ j ω, X j ω = 0 ∨ X j ω = 1) (G : Fin (N + 1) → MeasurableSpace Ω)
    (hGmono : Monotone G) (hGle : ∀ k, G k ≤ mΩ) (hXmeas : ∀ j, Measurable[G j.succ] (X j)) :
    ((∀ j : Fin N, condExp (G j.castSucc) μ ({ω | X j ω = 1}.indicator fun _ => (1 : ℝ))
        ≤ᵐ[μ] fun _ => (p : ℝ)) →
      ∀ y : ℝ, μ {ω | y ≤ ∑ j, X j ω} ≤
        (PMF.binomial p hp N).toOuterMeasure {k | y ≤ ((k : ℕ) : ℝ)}) ∧
    ((∀ j : Fin N, (fun _ => (p : ℝ)) ≤ᵐ[μ]
        condExp (G j.castSucc) μ ({ω | X j ω = 1}.indicator fun _ => (1 : ℝ))) →
      ∀ y : ℝ, μ {ω | ∑ j, X j ω < y} ≤
        (PMF.binomial p hp N).toOuterMeasure {k | ((k : ℕ) : ℝ) < y}) := by sorry

end PFRelease

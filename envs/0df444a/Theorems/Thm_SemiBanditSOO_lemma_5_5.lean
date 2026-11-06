-- Prove2me | Theorems.Thm_SemiBanditSOO_lemma_5_5
-- name    : SemiBanditSOO.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:59:34.687407+00:00
-- url     : https://prove2.me/theorems/8115042b-88fe-446f-a0e1-d88d8af85284
-- title:
--   Lemma 5.5 — one-sided bound $\mathbb E_Q\phi-\mathbb E_P\phi\le24\sqrt{\frac{k\Lambda\log(m+1)}{m+1}\mathrm{Var}_P\phi}+\frac{417k\Lambda}{m+1}$ when $P$ has $\le k$ support points
-- statement:
--   Let $k\ge1$ and $m\ge0$ be integers, and let $P,Q\in\mathcal C_m(\widehat D_{i,m})$, where $P$ has at most $k$ support points. Then, for every measurable $[0,1]$-valued function $\phi$,
--   $$\mathbb E_{X\sim Q}[\phi(X)]-\mathbb E_{X\sim P}[\phi(X)]\le24\sqrt{\frac{k\Lambda\log(m+1)}{m+1}\mathrm{Var}_{X\sim P}(\phi(X))}+\frac{417k\Lambda}{m+1}.$$
--
--   No condition on $\phi$ is needed here; this is what makes the regret depend on $\min\{s_i,k_i\}$.
--
--   **Formalization Note.** As in Lemma 5.4; "at most $k$ support points" means that some set of at most $k$ points has full $P$-mass.
--
--   Differences from the source:
--   - encoding: D̂_{i,m}, the empirical distribution of the first m revealed values of coordinate i → the empirical frequency of an arbitrary list L of m points of the domain; reason: the lemma is used for every sample; only the values of the sample enter
--   - encoding: distributions on the domain dom(i) ⊆ [0, 1] → ProbabilityMeasure on the subtype dom i with the subspace σ-algebra; reason: no measurability of dom(i) ⊆ ℝ is needed; the same distributions
--   - encoding: Λ, the quantity of §3.1 → Lam n T δ = log(80n(T + 1)³/δ) with 1 ≤ n, 1 ≤ T, δ ∈ (0, 1) as binders; reason: Λ is defined from n, T, δ on p.9
--   - encoding: P has at most k support points → supportCount P ≤ k, i.e. some finite set of at most k points has full mass; reason: the proof takes A the support of P with P(A) = 1; the same distributions
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, Lemma 5.5, p.23

import Mathlib
import Definitions.Def_SemiBanditSOO_LevelSet
import Definitions.Def_SemiBanditSOO_ConfidenceSet

open MeasureTheory

namespace SemiBanditSOO

/-- **Lemma 5.5 (one-sided bound for few support points).** Harada, Kawase, Sumita, *Beyond
Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1,
Lemma 5.5, p.23.

Let `k ≥ 1` and `m ≥ 0` be integers, and let `P, Q ∈ 𝒞_m(D̂_{i,m})`, where `P` has at most `k`
support points. Then, for every measurable `[0, 1]`-valued function `ϕ`,
`𝔼_{X∼Q}[ϕ(X)] − 𝔼_{X∼P}[ϕ(X)] ≤ 24 √(kΛ log(m + 1)/(m + 1) · Var_{X∼P}(ϕ(X))) + 417 kΛ/(m + 1)`.

**Formalization Note.** As in Lemma 5.4; "at most `k` support points" is `supportCount P ≤ k`
(some finite set of at most `k` points has full mass). -/
theorem lemma_5_5 {dom : Set ℝ} (hdom : dom ⊆ Set.Icc 0 1) (n T : ℕ) (δ : ℝ) (hn : 1 ≤ n)
    (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ < 1) (k : ℕ) (hk : 1 ≤ k) (L : List dom)
    (P Q : ProbabilityMeasure dom) (hP : P ∈ confSet (Lam n T δ) L)
    (hQ : Q ∈ confSet (Lam n T δ) L) (hsupp : supportCount (P : Measure dom) ≤ k)
    (ϕ : dom → ℝ) (hϕ : Measurable ϕ) (hϕ01 : ∀ z, ϕ z ∈ Set.Icc (0 : ℝ) 1) :
    ∫ z, ϕ z ∂(Q : Measure dom) - ∫ z, ϕ z ∂(P : Measure dom) ≤
      24 * Real.sqrt (k * Lam n T δ * Real.log (L.length + 1) / (L.length + 1) *
          ProbabilityTheory.variance ϕ (P : Measure dom)) +
        417 * k * Lam n T δ / (L.length + 1) := by sorry

end SemiBanditSOO

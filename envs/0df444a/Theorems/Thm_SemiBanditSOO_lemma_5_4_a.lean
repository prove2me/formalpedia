-- Prove2me | Theorems.Thm_SemiBanditSOO_lemma_5_4_a
-- name    : SemiBanditSOO.lemma_5_4_a
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:59:31.548218+00:00
-- url     : https://prove2.me/theorems/7bdfb98c-09fa-43b7-9134-7900a0633513
-- title:
--   Lemma 5.4(a) — $|Q(B)-P(B)|\le24\sqrt{P(B)(1-P(B))s\Lambda/m}+368s\Lambda/m$ for $B\in\mathcal I_s$
-- statement:
--   Let $s\ge1$ and $m\ge0$ be integers and $P,Q\in\mathcal C_m(\widehat D_{i,m})$. If $m\ge1$, then for every $B\in\mathcal I_s$,
--   $$|Q(B)-P(B)|\le24\sqrt{P(B)(1-P(B))\frac{s\Lambda}{m}}+368\frac{s\Lambda}{m}. \qquad (5.3)$$
--
--   Two distributions in the same confidence set are close on every union of a few intervals, with a variance-type leading term.
--
--   **Formalization Note.** The domain is any $\mathrm{dom}\subseteq[0,1]$, the sample is an arbitrary list of $m$ points of it, and $\Lambda=\log(80n(T+1)^3/\delta)$ with $n,T\ge1$ and $\delta\in(0,1)$.
--
--   Differences from the source:
--   - encoding: D̂_{i,m}, the empirical distribution of the first m revealed values of coordinate i → the empirical frequency of an arbitrary list L of m points of the domain; reason: the lemma is used for every sample; only the values of the sample enter
--   - encoding: distributions on the domain dom(i) ⊆ [0, 1] → ProbabilityMeasure on the subtype dom i with the subspace σ-algebra; reason: no measurability of dom(i) ⊆ ℝ is needed; the same distributions
--   - encoding: Λ, the quantity of §3.1 → Lam n T δ = log(80n(T + 1)³/δ) with 1 ≤ n, 1 ≤ T, δ ∈ (0, 1) as binders; reason: Λ is defined from n, T, δ on p.9
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, Lemma 5.4(a), (5.3), p.21

import Mathlib
import Definitions.Def_SemiBanditSOO_LevelSet
import Definitions.Def_SemiBanditSOO_ConfidenceSet

open MeasureTheory

namespace SemiBanditSOO

/-- **Lemma 5.4(a) (unions of intervals).** Harada, Kawase, Sumita, *Beyond Monotonicity:
Stochastic Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1, Lemma 5.4(a),
(5.3), p.21.

Let `s ≥ 1` and `m ≥ 0` be integers and `P, Q ∈ 𝒞_m(D̂_{i,m})`. If `m ≥ 1`, then for every
`B ∈ ℐ_s`, `|Q(B) − P(B)| ≤ 24 √(P(B)(1 − P(B)) sΛ/m) + 368 sΛ/m`.

**Formalization Note.** The coordinate's domain is any `dom ⊆ [0, 1]`; `D̂_{i,m}` is the empirical
distribution of an arbitrary sample `L` of `m` points of the domain; `Λ = log(80 n (T + 1)³/δ)` is
the quantity of §3.1, for `n ≥ 1`, `T ≥ 1`, `δ ∈ (0, 1)`. -/
theorem lemma_5_4_a {dom : Set ℝ} (hdom : dom ⊆ Set.Icc 0 1) (n T : ℕ) (δ : ℝ) (hn : 1 ≤ n)
    (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ < 1) (s : ℕ) (hs : 1 ≤ s) (L : List dom)
    (hm : 1 ≤ L.length) (P Q : ProbabilityMeasure dom) (hP : P ∈ confSet (Lam n T δ) L)
    (hQ : Q ∈ confSet (Lam n T δ) L) :
    ∀ B ∈ IntervalUnions s, |probOf Q B - probOf P B| ≤
      24 * Real.sqrt (probOf P B * (1 - probOf P B) * s * Lam n T δ / L.length) +
        368 * s * Lam n T δ / L.length := by sorry

end SemiBanditSOO

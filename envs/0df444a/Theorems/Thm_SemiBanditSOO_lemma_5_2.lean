-- Prove2me | Theorems.Thm_SemiBanditSOO_lemma_5_2
-- name    : SemiBanditSOO.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:59:25.104198+00:00
-- url     : https://prove2.me/theorems/58b480e1-7d29-42ef-83e2-99efba041ec5
-- title:
--   Lemma 5.2 — with probability $\ge1-\delta$, $D_i\in\mathcal C_m(\widehat D_{i,m})$ for all $i\in[n]$ and $0\le m\le T$
-- statement:
--   For each coordinate $i$ let $Z_{i,1},Z_{i,2},\dots$ be i.i.d. with distribution $D_i$, independently across coordinates, and let $\widehat D_{i,m}$ be the empirical distribution of $Z_{i,1},\dots,Z_{i,m}$. Let $\delta\in(0,1)$ and $\Lambda=\log(80n(T+1)^3/\delta)$. With probability at least $1-\delta$,
--   $$D_i\in\mathcal C_m(\widehat D_{i,m})\quad\text{simultaneously for every } i\in[n] \text{ and every } 0\le m\le T.$$
--
--   In the analysis the $j$-th revealed value of coordinate $i$ is $Z_{i,j}$, so this lemma makes the confidence sets of Algorithm 1 contain the true distributions in every round, outside an event of probability at most $\delta$.
--
--   **Formalization Note.** Only $Z_{i,1},\dots,Z_{i,T}$ enter, so each sequence is a vector of length $T$ under the product measure, and $\widehat D_{i,m}$ is the empirical distribution of its first $m$ entries.
--
--   Differences from the source:
--   - encoding: infinite i.i.d. sequences Z_{i,1}, Z_{i,2}, … → the first T terms, Z i : Fin T → dom i, under the product measure; reason: only m ≤ T samples enter the statement
--   - encoding: distributions on the domain dom(i) ⊆ [0, 1] → ProbabilityMeasure on the subtype dom i with the subspace σ-algebra; reason: no measurability of dom(i) ⊆ ℝ is needed; the same distributions
--   - encoding: n random variables X_1, …, X_n → hypothesis 1 ≤ n; reason: Λ = log(80n(T + 1)³/δ) is defined only for n ≥ 1; n = 0 is not a problem of the paper
--   - encoding: T rounds → T : ℕ with 1 ≤ T; reason: the number of rounds is a positive integer
--   - encoding: with probability at least 1 − η → the (outer) measure of the failure event is at most η; reason: the same statement; no measurability of the failure event needs to be proved
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, Lemma 5.2, p.20; the i.i.d. representation, §5.1, p.20

import Mathlib
import Definitions.Def_SemiBanditSOO_LevelSet
import Definitions.Def_SemiBanditSOO_ConfidenceSet

open MeasureTheory

namespace SemiBanditSOO

/-- **Lemma 5.2 (coverage of the confidence sets).** Harada, Kawase, Sumita, *Beyond Monotonicity:
Stochastic Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1, Lemma 5.2, p.20.

For each coordinate `i` let `Z_{i,1}, Z_{i,2}, …` be i.i.d. with distribution `D_i`, independently
across coordinates (§5.1, p.20), and let `D̂_{i,m}` be the empirical distribution of
`Z_{i,1}, …, Z_{i,m}`. With probability at least `1 − δ`, `D_i ∈ 𝒞_m(D̂_{i,m})` simultaneously for
every `i ∈ [n]` and every `0 ≤ m ≤ T`, where `Λ = log(80 n (T + 1)³/δ)`.

**Formalization Note.** Only the first `T` terms of each sequence enter, so the sequences are
`Z i : Fin T → dom i` under the product measure; `D̂_{i,m}` is the empirical distribution of the
first `m` entries. "With probability at least `1 − δ`" is stated as: the (outer) measure of the
failure event is at most `δ`. -/
theorem lemma_5_2 {n : ℕ} (dom : Fin n → Set ℝ) (hdom : ∀ i, dom i ⊆ Set.Icc 0 1)
    (D : ∀ i, ProbabilityMeasure (dom i)) (T : ℕ) (δ : ℝ) (hn : 1 ≤ n) (hT : 1 ≤ T)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun i => Measure.pi fun _ : Fin T => (D i : Measure (dom i)))
      {Z | ∃ i, ∃ m ≤ T, D i ∉ confSet (Lam n T δ) ((List.ofFn (Z i)).take m)}
      ≤ ENNReal.ofReal δ := by sorry

end SemiBanditSOO

-- Prove2me | Theorems.Thm_SublinearSteiner_Supplement_theorem_1_2
-- name    : SublinearSteiner.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:01:07.059197+00:00
-- url     : https://prove2.me/theorems/a60319ba-710d-4cb4-a1a6-c54b60c90c87
-- title:
--   Theorem 1.2 — every randomized $(2-\eta)$-estimator of the metric Steiner tree cost makes $\Omega(n^{(3s+7)/(2s+5)})$ expected queries
-- statement:
--   An instance of the metric Steiner tree problem is a set $V$ of $n$ points, a metric $w$ on $V$ and a set $T\subseteq V$ of terminals; $\mathrm{OPT}$ is the least weight of a tree in the complete graph on $V$ whose vertex set contains $T$. An **estimate within factor $2-\eta$** is a number $\widehat C$ with
--   $$
--   \mathrm{OPT}\le\widehat C\le(2-\eta)\,\mathrm{OPT}. \tag{1.1}
--   $$
--   Algorithms work in the distance-oracle model: they know $V$ and $T$, query pairs of points to learn their distance, and pay one unit per query.
--
--   **Theorem (lower bound).** For every $\eta\in(0,1)$ and every integer $s\ge1$ there are constants $c_{\eta,s}>0$ and $n_{\eta,s}$ such that the following holds for every $n\ge n_{\eta,s}$. Every randomized algorithm that, on every $n$-point instance, outputs with probability at least $2/3$ a number $\widehat C$ satisfying (1.1) makes at least
--   $$
--   c_{\eta,s}\, n^{b_s},\qquad b_s=\frac{3s+7}{2s+5}=\frac32-\frac1{4s+10},
--   $$
--   queries in expectation on some $n$-point instance.
--
--   Together with the $\tilde O(n^{3/2})$ upper bound of Theorem 1.1, letting $s\to\infty$ shows that the exponent $3/2$ of the query complexity of estimation below factor $2$ is tight.
--
--   **Formalization Note** A randomized algorithm is a probability space $(\Omega,\mu)$ of arbitrary type together with a map $\omega\mapsto A_\omega$ into deterministic adaptive query strategies (`QueryStrategy n`, arbitrary functions of $T$ and the query history). The expected query count is the Lebesgue integral in $[0,\infty]$ of the query count, and a run that never outputs counts as infinitely many queries and as a failure. The constants $c$ and $N$ are chosen before $n$ and the algorithm.
--
--   Differences from the source:
--   - encoding: every randomized algorithm in the distance-oracle model → a probability space (Ω, μ) of any type with a map to arbitrary deterministic adaptive query strategies on Fin n; reason: a randomized query algorithm is a random choice of deterministic adaptive strategy; no computability, machine or finite-support restriction is imposed
--   - encoding: probability of success and expected number of queries → the query count is assumed a.e.-measurable and the success event null-measurable in ω, for each instance; reason: this excludes only algorithms for which the page's probability or expectation is undefined; every algorithm on a countable Ω with the discrete σ-algebra satisfies it
--   - encoding: expected number of queries → lower Lebesgue integral in ℝ≥0∞ of an ℕ∞-valued count, with ⊤ for a run that never outputs; reason: Lean convention for an expectation of a nonnegative, possibly infinite quantity; same instances
--   - encoding: queries of unordered pairs {u, v} → queries of ordered pairs (u, v), each counted, including repeats and pairs (u, u); reason: an algorithm in the page's model is one of these with the same count, so the class only grows
--   - encoding: an n-point instance (V, w, T) with OPT → V = Fin n, w : FinMetric n, any T : Finset (Fin n), OPT given by IsSteinerOpt T w OPT; reason: the published instance layer of the base mission; same instances
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Theorem 1.2, p.1 (PDF p.2); (1.1), p.1; proof in §§5–7, pp.28–53, completed in §7.3, p.53

import Mathlib
import Definitions.Def_SublinearSteiner_FinMetric
import Definitions.Def_SublinearSteiner_Supplement_QueryStrategy

open scoped Classical ENNReal

open MeasureTheory

namespace SublinearSteiner

namespace Supplement

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission
(manuscript sha256 ae133037…), Theorem 1.2 (Lower bound), p.1, with (1.1), p.1. For every `η ∈ (0, 1)` and every
integer `s ≥ 1` there are constants `c > 0` and `N` such that for every `n ≥ N`, every randomized algorithm that,
on every `n`-point instance, outputs with probability at least `2/3` a number `Ĉ` with
`OPT ≤ Ĉ ≤ (2 − η) OPT` makes at least `c · n ^ b_s` queries in expectation on some `n`-point instance, where
`b_s = (3s + 7)/(2s + 5)`.

**Formalization Note.**
* A randomized algorithm is a probability space `(Ω, μ)` (any type, any σ-algebra) and a map `A` from `Ω` to
  deterministic adaptive query strategies (`QueryStrategy n`: an arbitrary function of `T` and the query history).
  Correlated or uncountable randomness is allowed.
* For each instance, the query count and the success event are assumed a.e.-measurable / null-measurable in `ω`,
  so that the expectation and the probability are the usual ones. Every algorithm with countable `Ω` and the
  discrete σ-algebra satisfies this.
* The expected query count is the lower Lebesgue integral in `ℝ≥0∞` of the `ℕ∞`-valued count; a run that never
  outputs counts `⊤` queries and fails.
* An instance is `w : FinMetric n` and `T : Finset (Fin n)`; `OPT` is given by `IsSteinerOpt T w OPT`.
* `c` and `N` depend only on `η` and `s`; the exponent is the exact real number `(3s + 7)/(2s + 5)`. -/
theorem theorem_1_2 (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (s : ℕ) (hs : 1 ≤ s) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Ω → QueryStrategy n),
        (∀ (T : Finset (Fin n)) (w : FinMetric n),
          AEMeasurable (fun ω => ((A ω).queryCount T w : ℝ≥0∞)) μ) →
        (∀ (T : Finset (Fin n)) (w : FinMetric n) (OPT : ℝ),
          NullMeasurableSet {ω | ∃ z : ℝ, (A ω).output T w = some z ∧ OPT ≤ z ∧ z ≤ (2 - η) * OPT} μ) →
        (∀ (T : Finset (Fin n)) (w : FinMetric n) (OPT : ℝ), IsSteinerOpt T w OPT →
          (2 / 3 : ℝ≥0∞) ≤
            μ {ω | ∃ z : ℝ, (A ω).output T w = some z ∧ OPT ≤ z ∧ z ≤ (2 - η) * OPT}) →
        ∃ (T : Finset (Fin n)) (w : FinMetric n),
          ENNReal.ofReal (c * (n : ℝ) ^ (((3 * s + 7 : ℕ) : ℝ) / ((2 * s + 5 : ℕ) : ℝ))) ≤
            ∫⁻ ω, ((A ω).queryCount T w : ℝ≥0∞) ∂μ := by sorry

end Supplement

end SublinearSteiner

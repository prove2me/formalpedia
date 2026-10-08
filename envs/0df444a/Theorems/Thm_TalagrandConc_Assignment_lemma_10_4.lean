-- Prove2me | Theorems.Thm_TalagrandConc_Assignment_lemma_10_4
-- name    : TalagrandConc.Assignment.lemma_10_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:21.430659+00:00
-- url     : https://prove2.me/theorems/3ec682a6-337a-4be8-be15-ba446a38edbc
-- title:
--   Lemma 10.4 — fewer than δpN of N independent events of probability p occur with probability ≤ exp(−Np/K(δ))
-- statement:
--   For every $\delta < 1$ there is a constant $K(\delta) > 0$, depending on $\delta$ only, with the following property. Let $(\Omega, P)$ be a probability space, $N \ge 0$, and $A_1, \dots, A_N$ independent events with $P(A_i) = p$ for all $i$. Then
--   $$P\big(\operatorname{card}\{ i \le N ;\ \omega \in A_i \} < \delta p N\big) \le \exp\Big(-\frac{Np}{K(\delta)}\Big).$$
--
--   This is a lower-tail Chernoff bound for a binomial count with a constant uniform in $N$ and $p$; in the chapter it yields Eq. (10.5), the lower bound on $\operatorname{card} D_u(S)$ for a fixed set $S$.
--
--   **Formalization Note** $K(\delta)$ is chosen before $\Omega$, $P$, $N$, $p$ and the events. Independence is Mathlib's `iIndepSet`; the events are measurable. A related but different platform statement is `BanditAlgorithm.bernoulli_chernoff_tail_bound` (KL form).
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 168, Lemma 10.4

import Mathlib

namespace TalagrandConc.Assignment

open MeasureTheory ProbabilityTheory

/-- Talagrand (1995), p. 168, Lemma 10.4. For every `δ < 1` there is `K(δ) > 0`, depending
on `δ` only, such that for independent events `A_1, …, A_N` with `P(A_i) = p`, the
probability that fewer than `δ p N` of the events occur is at most `exp(−N p / K(δ))`. -/
theorem lemma_10_4 :
    ∀ δ : ℝ, δ < 1 → ∃ K : ℝ, 0 < K ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : ℕ) (A : Fin N → Set Ω) (p : ℝ),
        (∀ i, MeasurableSet (A i)) → iIndepSet A P → (∀ i, P.real (A i) = p) →
        P {ω | (({i : Fin N | ω ∈ A i}.ncard : ℕ) : ℝ) < δ * p * N} ≤
          ENNReal.ofReal (Real.exp (-((N : ℝ) * p) / K)) := by sorry

end TalagrandConc.Assignment

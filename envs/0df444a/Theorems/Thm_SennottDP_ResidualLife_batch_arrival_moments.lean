-- Prove2me | Theorems.Thm_SennottDP_ResidualLife_batch_arrival_moments
-- name    : SennottDP.ResidualLife.batch_arrival_moments
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T10:40:28.965257+00:00
-- url     : https://prove2.me/theorems/083c84dc-6966-4ed4-aa7e-316d4ae3291c
-- title:
--   Lemma 9.5.2 — first and second moments of the number of batch arrivals in s slots
-- statement:
--   In each slot a batch of customers arrives; the batch sizes $X_1, X_2, \dots$ in successive slots are independent and identically distributed with $P(X_k = j) = p_j$, $j \ge 0$, mean $\lambda = \sum_j j p_j$ and second moment $\lambda^{(2)} = \sum_j j^2 p_j$. Assume (BA1): $\lambda^{(2)} < \infty$. Let $X(s) = \sum_{k=1}^{s} X_k$ be the number of customers arriving in $s$ slots. Then, for every $s \ge 0$,
--   $$E[X(s)] = \lambda s, \qquad E[(X(s))^2] = \lambda^{(2)} s + \lambda^2 s(s-1).$$
--
--   These expressions show that the expected arrivals over $s$ slots are linear in $s$ and their second moment is quadratic in $s$, which is what the verification of the average cost assumptions for the batch-arrival queue of Example 9.3.1 needs.
--
--   **Formalization Note** The batch sizes are measurable functions $X_k : \Omega \to \mathbb N$ on a probability space, mutually independent (`iIndepFun`) with common law $p$; the slots are indexed $0,\dots,s-1$. Expectations are lower Lebesgue integrals in $[0,\infty]$, and $\lambda$, $\lambda^{(2)}$ are the `ℝ≥0∞`-valued series $\sum_j j p_j$, $\sum_j j^2 p_j$. Of the book's assumptions (BA1)–(BA5) (p. 214) only (BA1) concerns arrivals; (BA2)–(BA5) concern the service times and the costs, do not involve $X(s)$, and are omitted, so the statement holds under (BA1) alone. $s(s-1)$ is computed in $\mathbb N$ (it is $0$ for $s = 0$).
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 215, Lemma 9.5.2, Eq. (9.25); assumptions (BA1)–(BA5), p. 214; batch arrivals, Example 9.3.1, p. 207

import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace SennottDP.ResidualLife

/-- Sennott (1999), Lemma 9.5.2, p. 215, (9.25): batches arrive in each slot, independently from slot
to slot, with common distribution `p_j = P(batch size = j)`, mean `λ = ∑_j j p_j` and second moment
`λ^{(2)} = ∑_j j² p_j < ∞` (assumption (BA1), p. 214). If `X(s) = X_1 + ⋯ + X_s` is the number of
customers arriving in `s` slots, then `E[X(s)] = λ s` and `E[X(s)²] = λ^{(2)} s + λ² s (s - 1)`. -/
theorem batch_arrival_moments {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ℕ → ℝ≥0∞) (X : ℕ → Ω → ℕ) (hXmeas : ∀ k, Measurable (X k))
    (hindep : iIndepFun X P) (hlaw : ∀ k j, P (X k ⁻¹' {j}) = p j)
    (hBA1 : moment p 2 < ∞) (s : ℕ) :
    ∫⁻ ω, (∑ k ∈ Finset.range s, (X k ω : ℝ≥0∞)) ∂P = moment p 1 * s ∧
    ∫⁻ ω, (∑ k ∈ Finset.range s, (X k ω : ℝ≥0∞)) ^ 2 ∂P =
      moment p 2 * s + moment p 1 ^ 2 * ((s * (s - 1) : ℕ) : ℝ≥0∞) := by sorry

end SennottDP.ResidualLife

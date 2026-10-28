-- Prove2me | Theorems.Thm_SeqRankAgg_Optimality_lemma_8
-- name    : SeqRankAgg.Optimality.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:43.898981+00:00
-- url     : https://prove2.me/theorems/48b062c7-b5a4-4dbb-8c08-2c8872b07574
-- title:
--   Lemma 8, p. 22 — Azuma–Hoeffding inequality for the running maximum of a martingale
-- statement:
--   Let $(M_n)_{n\ge0}$ be a real martingale with respect to a filtration $(\mathcal F_n)$ on a probability space $(\Omega,\mathcal F,\mathbb P)$, started at $M_0=0$. Suppose its increments $X_n=M_n-M_{n-1}$ satisfy $a_n\le X_n\le b_n$ almost surely, for deterministic constants $a_n\le b_n$. Then for every $n\ge1$ and every $t>0$,
--
--   $$
--   \mathbb P\Big(\max_{1\le k\le n}M_k\ge t\Big)\le\exp\Big(-\frac{2t^2}{\sum_{i=1}^n(b_i-a_i)^2}\Big).
--   $$
--
--   This maximal form of the Azuma–Hoeffding inequality is the concentration tool the paper applies to the log-likelihood martingales in the lower-bound and sample-size arguments.
--
--   **Formalization Note** The page leaves $M_0$ implicit; the Lean statement assumes $M_0=0$ almost surely, without which the bound fails (a constant martingale $M_n\equiv M_0>t$). Time is indexed from $0$ and the increment bounds are indexed by the later time. If $\sum_i(b_i-a_i)^2=0$, Lean's division gives the trivial bound $1$.
-- source:
--   Chen, Chen & Li, Asymptotically optimal sequential design for rank aggregation, arXiv:1710.06056v1, p. 22, Lemma 8 (Azuma 1967; Hoeffding 1963)

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace SeqRankAgg.Optimality

theorem lemma_8 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (M : ℕ → Ω → ℝ) (hM : Martingale M ℱ P)
    (hM0 : ∀ᵐ ω ∂P, M 0 ω = 0)
    (a b : ℕ → ℝ)
    (hinc : ∀ k : ℕ, ∀ᵐ ω ∂P, M (k + 1) ω - M k ω ∈ Set.Icc (a (k + 1)) (b (k + 1)))
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    P {ω | ∃ k ∈ Finset.Icc 1 n, t ≤ M k ω} ≤
      ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / ∑ i ∈ Finset.Icc 1 n, (b i - a i) ^ 2))) := by sorry

end SeqRankAgg.Optimality

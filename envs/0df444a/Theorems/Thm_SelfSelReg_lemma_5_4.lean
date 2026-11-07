-- Prove2me | Theorems.Thm_SelfSelReg_lemma_5_4
-- name    : SelfSelReg.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:08.664527+00:00
-- url     : https://prove2.me/theorems/dbfaffed-abc0-4552-98ea-2be932cec725
-- title:
--   Lemma 5.4 — a large response is rarely exceeded: $\mathbb P(Y_{\max,Q}>t\mid Y_i=t)\le ke^{-2t^2/K}$
-- statement:
--   In the Gaussian self-selection model ($n\ge1$, $2\le k\le n$) under Assumption 1.2 with constants $B\ge1$, $\Delta\in(0,1]$, let $K$ and $T$ be the hyperparameters of Hyperparameters 4.1. For every non-empty $Q\subseteq[k]$, every $i\in Q$ and every $t\in[T,T+1]$,
--   $$\mathbb P\big(Y_{\max,Q}>t\ \big|\ Y_i=t\big)\le k\,e^{-2t^2/K}.$$
--
--   On the slice, the response that lies in it is with high probability the maximum among the remaining responses; this controls the error of replacing the slice of the maximum by the sum of single-response slices.
--
--   **Formalization Note** The conditional probability is taken under the explicit conditional law `modelCondLaw` of Proposition 4.3; $Y_{\max,Q}>t$ means that some $Y_j$, $j\in Q$, exceeds $t$.
--
--   Differences from the source:
--   - reading: s := K⁴ log n (9), printed as a real number → s = ⌈K⁴ log n⌉ (hypS), natural logarithm; reason: s is used as a tensor order ("let s ≥ 1 be an integer", Lemmas 5.7, 5.8) and (182) states s ≤ 2K⁴ log n, which presupposes rounding up; the ceiling is also the stronger choice for every bound that improves with s
--   - encoding: E[· | Y_i = t] and P(· | Y_i = t) for every t → integrals and measures under modelCondLaw w i t, the pushforward of the model law under (x, ξ) ↦ (x − c w_i, ξ − c e_i), c = (Y_i − t)/σ_i²; reason: this is the conditional Gaussian law of Proposition 4.3 for the jointly Gaussian vector (X, ξ, Y_i), defined for every t instead of almost everywhere
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Lemma 5.4, p.20 (PDF p.23)

import Mathlib
import Definitions.Def_SelfSelReg_jointLaw
import Definitions.Def_SelfSelReg_SatisfiesAssumption
import Definitions.Def_SelfSelReg_hypK
import Definitions.Def_SelfSelReg_modelCondLaw

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- **Lemma 5.4** (A Large Response Is Rarely Exceeded).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Lemma 5.4, p.20 (PDF p.23): "Consider the Gaussian self-selection model
(Definition 1.1) under the boundedness and uncoveredness assumptions (Assumption 1.2). Use the
hyperparameters K, T, s from Hyperparameters 4.1. For every non-empty Q ⊆ [k], i ∈ Q, and
t ∈ [T, T + 1], P(Y_max,Q > t | Y_i = t) ≤ k e^{−2t²/K}."

**Formalization Note.** `K = hypK B ∆`, `T = hypT B ∆ n` (with `s = ⌈K⁴ log n⌉`). `P(· | Y_i = t)` is
the explicit conditional law `modelCondLaw w i t` (Proposition 4.3), defined for every `t`.
`Y_max,Q > t` is "some `Y_j`, `j ∈ Q`, exceeds `t`". -/
theorem lemma_5_4 (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (B Δ : ℝ) (hB : 1 ≤ B)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (w : Fin k → EuclideanSpace ℝ (Fin n))
    (hw : SatisfiesAssumption B Δ w) (Q : Finset (Fin k)) (hQ : Q.Nonempty) (i : Fin k)
    (hi : i ∈ Q) (t : ℝ) (ht : hypT B Δ n ≤ t) (ht' : t ≤ hypT B Δ n + 1) :
    (modelCondLaw w i t).real
        {z | ∃ j ∈ Q, t < response w z.1 z.2 j} ≤
      (k : ℝ) * Real.exp (-2 * t ^ 2 / hypK B Δ) := by sorry

end SelfSelReg

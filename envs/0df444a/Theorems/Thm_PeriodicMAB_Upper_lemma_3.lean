-- Prove2me | Theorems.Thm_PeriodicMAB_Upper_lemma_3
-- name    : PeriodicMAB.Upper.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:42.880533+00:00
-- url     : https://prove2.me/theorems/461a34eb-d6d1-4224-8a23-b06b1619da43
-- title:
--   Lemma 3, p. 18 — $B_k\le(\sup|\tilde\epsilon_k|+\sup|\tilde y_k|)/(1-\pi U_2)$
-- statement:
--   Under the hypotheses of Lemma 2 (a mean sequence $\mu_k$ of minimum period $T_k$ and Assumption 3 for this arm), for every realization of the noise,
--   $$
--   B_k\le\frac{1}{1-\pi U_2}\Big(\sup_{v\in[0,1/2]}|\tilde\epsilon_k(v)|+\sup_{v\in[0,1/2]}|\tilde y_k(v)|\Big).
--   $$
--
--   This is the data-driven upper bound on the unknown $B_k$ that justifies the threshold $\tau_k$ of Algorithm 1.
--
--   **Formalization Note** The statement is deterministic: it holds for every noise path. The two suprema are suprema of continuous functions over $[0,1/2]$, written as `sSup` of their images.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 18, Lemma 3

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-- Lemma 3 (p. 18): pathwise, `B_k ≤ (1/(1 − πU₂)) (sup_{[0,1/2]} |ε̃_k| + sup_{[0,1/2]} |ỹ_k|)`. -/
theorem lemma_3 {Ω : Type*} (μk : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (p n g k : ℕ)
    (hper : IsMinPeriod μk p) (hA3 : Assumption3Arm n g p) (ω : Ω) :
    bigB μk p ≤ 1 / (1 - Real.pi * U2 n g) * (supEps ε n k ω + supY μk ε n k ω) := by sorry

end PeriodicMAB.Upper

-- Prove2me | Theorems.Thm_UnknownCovDP_General_claim_2_8
-- name    : UnknownCovDP.General.claim_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:19.220611+00:00
-- url     : https://prove2.me/theorems/82424b36-8576-4ec8-af7c-19c599721542
-- title:
--   Claim 2.8 — the average test value on the good event
-- statement:
--   Let $n\ge1$, $C,\lambda,\alpha>0$, and suppose $\alpha\le\lambda\sqrt{d/(4Ck)}$. If $(\Sigma,X,y)$ lies in $G=G_1\cap G_2\cap G_3$, then
--   $$\mathbb E_{i}\bigl[T_{\Sigma,y}(x_i)\bigr]\ge\frac{k}{4n},$$
--   where $\mathbb E_i$ is the uniform average over $i\in[n]$.
--
--   This is a deterministic statement: on $G$, some data point scores high.
--
--   Differences from the source:
--   - reading: C and λ, α introduced by the surrounding proof and Definition 2.2 → explicit parameters with 0 < C, 0 < lam, 0 < α; reason: the claim uses the constants of the proof of Lemma 2.7, and Definition 2.2 fixes α, λ > 0
--   - encoding: n is a sample size, with division by n in the empirical covariance and test averages → hypothesis 1 ≤ n; reason: these sample averages are defined for positive sample size; the source does not use c/n in this result
--   - encoding: 𝔼_i, the expectation over uniform i ∈ [n] → (1/n) ∑ i; reason: the definition of the uniform average
--   - generalization: Σ, X, y from the experiment → every real d×d matrix S, every X, every y; reason: G is the only property the claim uses; the source's triples are particular instances
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Claim 2.8, printed p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_UnknownCovDP_General_TestEvents

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General

/-- Claim 2.8, printed p. 14, PDF p. 15. If `α ≤ lam √(d/(4Ck))` and `(S, X, y)` lies in `G`, then
`𝔼_i[T_{S,y}(x_i)] ≥ k/(4n)`, where `𝔼_i` is the uniform average over `i ∈ [n]`. -/
theorem claim_2_8 {d k n : ℕ} (hn : 1 ≤ n) {C lam α : ℝ} (hC : 0 < C) (hlam : 0 < lam)
    (hα : 0 < α) (hαle : α ≤ lam * Real.sqrt ((d : ℝ) / (4 * C * k)))
    (S : Mat d) (X : Fin n → Vec d) (y : Vec d) (hG : EventG k C lam α S X y) :
    (k : ℝ) / (4 * n) ≤ (n : ℝ)⁻¹ * ∑ i, testStat S y (X i) := by sorry

end UnknownCovDP.General

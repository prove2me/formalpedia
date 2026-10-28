-- Prove2me | Theorems.Thm_SLPEPricing_Regret_hoeffding_step
-- name    : SLPEPricing.Regret.hoeffding_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:20.638246+00:00
-- url     : https://prove2.me/theorems/bdc805e7-93e6-4e34-89c0-432898052e03
-- title:
--   pp. 19–20, proof of Lemma 4 — the M-price average is within Δ²/ρ² of its mean w.p. ≥ 1 − 1/T² (repaired: σ² ≤ 1/3, T ≥ 2)
-- statement:
--   Let $X_1,\dots,X_n$ be independent random variables on a probability space $(\Omega,\mathcal F,\mathbb P)$, each sub-Gaussian with variance proxy $\sigma^2$, i.e. $\mathbb E[e^{tX_j}]\le e^{\sigma^2t^2/2}$ for all $t\in\mathbb R$ (in particular $\mathbb E X_j=0$). Let $\rho,\Delta>0$, $T\ge2$ an integer, and $n\ge1$ with
--   $$n\ \ge\ \frac{2\rho^4\log T}{\Delta^4}.$$
--   If $\sigma^2\le 1/3$, then
--   $$\mathbb P\left(\Big|\frac1n\sum_{j=1}^nX_j\Big|>\frac{\Delta^2}{\rho^2}\right)\le\frac1{T^2}.$$
--
--   In the proof of Lemma 4 the $X_j$ are the noise terms of the $n_i$ periods at the price $p^M_i$, so the statement bounds the probability that the concentration event $|\bar D_{n_i}(p^M_i)-d(p^M_i)|\le\Delta_i^2/\rho^2$ fails in a round.
--
--   **Formalization Note** The page claims the bound for $\sigma$-sub-Gaussian noise with no restriction on $\sigma$; that is false: for standard normal noise ($\sigma=1$) and $T=100$ the failure probability is $2.4\cdot10^{-3}>10^{-4}$. The two-sided sub-Gaussian bound gives $2T^{-1/\sigma^2}$, which is at most $T^{-2}$ exactly when $\sigma^2\le1/3$ (for $T\ge2$); these two hypotheses are added. The sub-Gaussian property is Mathlib's `HasSubgaussianMGF` with parameter $\sigma^2$; the noise index set is `Fin n`.
-- source:
--   Perakis & Singhvi, Dynamic Pricing with Unknown Non-Parametric Demand and Limited Price Changes, SSRN 3336949 (PDF of 2020-07-03), pp. 19–20, proof of Lemma 4, Step 2 (display 'w.p at least 1 − 1/T²' on p. 19 and the Hoeffding sentence on p. 20)

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SLPEPricing.Regret

/-- The Hoeffding step in the proof of Lemma 4 (pp. 19–20), repaired. Let `X_1, …, X_n` be
independent noise terms, each sub-Gaussian with variance proxy `σ² ≤ 1/3`, with
`n ≥ 2ρ⁴ log(T)/Δ⁴`, `n ≥ 1`, `ρ, Δ > 0` and `T ≥ 2`. Then the average of the `X_j` exceeds
`Δ²/ρ²` in absolute value with probability at most `1/T²`. -/
theorem hoeffding_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (X : Fin n → Ω → ℝ) (σsq : ℝ≥0)
    (hindep : iIndepFun X P) (hsub : ∀ j, HasSubgaussianMGF (X j) σsq P)
    (hσ : (σsq : ℝ) ≤ 1 / 3)
    (ρ Δ : ℝ) (hρ : 0 < ρ) (hΔ : 0 < Δ) (T : ℕ) (hT : 2 ≤ T)
    (hnT : 2 * ρ ^ 4 * Real.log (T : ℝ) / Δ ^ 4 ≤ (n : ℝ)) :
    P.real {ω | Δ ^ 2 / ρ ^ 2 < |(∑ j, X j ω) / (n : ℝ)|} ≤ 1 / (T : ℝ) ^ 2 := by sorry

end SLPEPricing.Regret

-- Prove2me | Theorems.Thm_PrivRobustStat_lemma_2
-- name    : PrivRobustStat.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:17.155719+00:00
-- url     : https://prove2.me/theorems/d27bc931-9697-410c-8808-79263d16e665
-- title:
--   Lemma 2, p.12 — weighted means of weights close in TV are close: $\|\hat\mu(v)-\hat\mu(w)\|_2^2\le\frac{2\rho}{1-2\rho}(\cdots)$
-- statement:
--   **Lemma 2** (spectral signatures). Let $x_{[n]}\subset\mathbb R^d$, $v,w\in\mathcal W$, and $\mathrm{TV}(v/\|v\|_1,w/\|w\|_1)\le\rho<\tfrac12$. Then
--
--   $$\|\hat\mu(v)-\hat\mu(w)\|_2^2\le\frac{2\rho}{1-2\rho}\Big(\frac{\|\hat\Sigma(v)\|_{\mathrm{op}}}{\|v\|_1}+\frac{\|\hat\Sigma(w)\|_{\mathrm{op}}}{\|w\|_1}\Big).$$
--
--   It turns a spectral bound on the filtered covariance into an accuracy bound for the filtered mean.
--
--   Differences from the source:
--   - encoding: ∥·∥_op → HighDimStat.Pca.opNormSymm, sup over unit vectors of |⟨v, Av⟩|; reason: equals the operator norm on symmetric matrices, and Σ̂(·) is symmetric
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Lemma 2, p.12 (PDF p.15); proof in Appendix A.2, p.75

import Mathlib
import Definitions.Def_PrivRobustStat_Model
import Definitions.Def_HighDimStat_Pca_OpNormSymm

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Lemma 2** (spectral signatures), p.12 (PDF p.15); proof in Appendix A.2, p.75.

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"If x[n] ⊂ R^d, v, w ∈ W, and TV(v/∥v∥₁, w/∥w∥₁) ≤ ρ < 1/2,
∥µ̂(v) − µ̂(w)∥₂² ≤ 2ρ/(1 − 2ρ) ( (1/∥v∥₁)∥Σ̂(v)∥_op + (1/∥w∥₁)∥Σ̂(w)∥_op )."

**Formalization Note.** `µ̂ = wMean`, `Σ̂(v) = Σ̂(v, µ̂(v)) = cov` (unnormalized, (8)), `TV = tvW`
(half the `ℓ₁` distance of the normalized weights), `∥·∥_op` is the published
`HighDimStat.Pca.opNormSymm` (the `ℓ²` operator norm of a symmetric matrix; `Σ̂` is symmetric). -/
theorem lemma_2 {d n : ℕ} (x : Fin n → Vec d) (v w : Fin n → ℝ) (hv : InW n v) (hw : InW n w)
    (ρ : ℝ) (hρ : tvW v w ≤ ρ) (hρ2 : ρ < 1 / 2) :
    ‖wMean x v - wMean x w‖ ^ 2 ≤
      2 * ρ / (1 - 2 * ρ) *
        (HighDimStat.Pca.opNormSymm (cov x v) / l1 v + HighDimStat.Pca.opNormSymm (cov x w) / l1 w) := by sorry

end PrivRobustStat

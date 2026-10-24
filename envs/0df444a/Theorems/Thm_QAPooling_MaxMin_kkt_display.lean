-- Prove2me | Theorems.Thm_QAPooling_MaxMin_kkt_display
-- name    : QAPooling.MaxMin.kkt_display
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:34.30051+00:00
-- url     : https://prove2.me/theorems/6a6212f9-6080-4a13-8c38-9dc16e033cd1
-- title:
--   Proof of Theorem 4.1, p. 14 — KKT: g(p*) = Σ wᵢ g(pᵢ) + λ1ₙ + µ with µ ≥ 0 and µⱼ = 0 where p*ⱼ > 0
-- statement:
--   Let $s$ be a regular proper scoring rule with exposure function $g$, such that $s(\cdot\,;j)$ is continuous on $\Delta^n$ for every $j$ and the expected reward $G$ is continuous on $\Delta^n$. Let $p_1,\dots,p_m\in\mathcal D$ with non-negative weights $w_i$ adding to $1$, and let $p^*$ be their QA pool. Then there are $\lambda\in\mathbb R$ and $\mu\in\mathbb R^n$ with
--   $$g(p^*)=\sum_{i=1}^m w_i\,g(p_i)+\lambda\mathbf 1_n+\mu,$$
--   such that $\mu_j\ge 0$ for every $j$ and $\mu_j=0$ whenever $p^*_j>0$.
--
--   These are the Karush–Kuhn–Tucker conditions for minimizing $G(x)-\langle x,\sum_i w_i g(p_i)\rangle$ over the simplex at its minimizer $p^*$, valid even when $p^*$ lies on the boundary of $\Delta^n$. They are the step of the proof of Theorem 4.1 that ties the pool's own exposure to the experts' exposures.
--
--   **Formalization Note** $g(p^*)$ is meaningful because $p^*\in\mathcal D$ (Claim 3.10). The continuity hypotheses are the paper's standing assumptions of p. 10.
-- source:
--   Neyman & Roughgarden, From Proper Scoring Rules to Max-Min Optimal Forecast Aggregation, arXiv:2102.07081v2, p. 14, proof of Theorem 4.1 (KKT display, footnote 14)

import Mathlib
import Definitions.Def_QAPooling_MaxMin_Model

namespace QAPooling.MaxMin

/-- KKT display in the proof of Theorem 4.1 (p. 14): `g(p*) = Σ_i w_i g(p_i) + λ 1_n + μ` for some
`λ ∈ ℝ` and `μ ∈ ℝⁿ` with `μ_j ≥ 0` and `μ_j = 0` whenever `p*_j > 0`. -/
theorem kkt_display {n m : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hreg : IsRegular s) (hprop : IsProper s)
    (hcont : ∀ j, ContinuousOn (fun p => s p j) (stdSimplex ℝ (Fin n)))
    (hGcont : ContinuousOn (expectedReward s) (stdSimplex ℝ (Fin n)))
    (hg : IsExposure s g)
    (p : Fin m → Fin n → ℝ) (hp : ∀ i, p i ∈ forecastDomain s)
    (w : Fin m → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (pstar : Fin n → ℝ) (hpstar : IsQAPool s g p w pstar) :
    ∃ (lam : ℝ) (mu : Fin n → ℝ),
      (∀ j, g pstar j = ∑ i, w i * g (p i) j + lam + mu j) ∧
      (∀ j, 0 ≤ mu j) ∧ (∀ j, 0 < pstar j → mu j = 0) := by sorry

end QAPooling.MaxMin

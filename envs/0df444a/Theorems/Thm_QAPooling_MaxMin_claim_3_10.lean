-- Prove2me | Theorems.Thm_QAPooling_MaxMin_claim_3_10
-- name    : QAPooling.MaxMin.claim_3_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:43.637533+00:00
-- url     : https://prove2.me/theorems/05626f1f-6523-4c18-a3bc-7f447927ae91
-- title:
--   Claim 3.10, p. 12 — the QA pool p* lies in the forecast domain D
-- statement:
--   Let $s$ be a regular proper scoring rule with exposure function $g$, such that $s(\cdot\,;j)$ is continuous on $\Delta^n$ (as a map into $\mathbb R\cup\{-\infty\}$) for every outcome $j$. Let $p_1,\dots,p_m\in\mathcal D$ be forecasts with non-negative weights $w_1,\dots,w_m$ adding to $1$, and let $p^*\in\Delta^n$ be a point at which $\sum_i w_i g(p_i)$ is a subgradient of $G$. Then
--   $$p^*\in\mathcal D,$$
--   that is, $s(p^*;j)$ is finite for every outcome $j$.
--
--   Definition 3.6 only places the QA pool in $\Delta^n$; this claim shows the pool never sits at a forecast that some outcome would score $-\infty$, so the agent's profit at $p^*$ in Theorem 4.1 is finite.
--
--   **Formalization Note** The continuity of each $s(\cdot\,;j)$ is the paper's standing assumption of p. 10, with the topology of footnote 11 (the order topology on the extended reals).
-- source:
--   Neyman & Roughgarden, From Proper Scoring Rules to Max-Min Optimal Forecast Aggregation, arXiv:2102.07081v2, p. 12, Claim 3.10 (proof p. 13)

import Mathlib
import Definitions.Def_QAPooling_MaxMin_Model

namespace QAPooling.MaxMin

/-- Claim 3.10 (p. 12): the QA pool `p*` of forecasts in `D` lies in `D`. -/
theorem claim_3_10 {n m : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hreg : IsRegular s) (hprop : IsProper s)
    (hcont : ∀ j, ContinuousOn (fun p => s p j) (stdSimplex ℝ (Fin n)))
    (hg : IsExposure s g)
    (p : Fin m → Fin n → ℝ) (hp : ∀ i, p i ∈ forecastDomain s)
    (w : Fin m → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (pstar : Fin n → ℝ) (hpstar : IsQAPool s g p w pstar) :
    pstar ∈ forecastDomain s := by sorry

end QAPooling.MaxMin

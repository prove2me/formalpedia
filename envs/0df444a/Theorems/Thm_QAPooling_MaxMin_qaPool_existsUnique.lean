-- Prove2me | Theorems.Thm_QAPooling_MaxMin_qaPool_existsUnique
-- name    : QAPooling.MaxMin.qaPool_existsUnique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:35.915588+00:00
-- url     : https://prove2.me/theorems/a2fe3759-e156-46f2-ba72-1dba93753ef0
-- title:
--   §3.2, p. 12 — the QA pool is well-defined: exactly one p* ∈ Δⁿ has Σᵢ wᵢ g(pᵢ) as a subgradient of G
-- statement:
--   Let $s$ be a regular proper scoring rule whose expected reward $G$ is continuous on $\Delta^n$, and let $g$ be an exposure function of $s$. Let $p_1,\dots,p_m\in\mathcal D$ be forecasts with non-negative weights $w_1,\dots,w_m$ adding to $1$. Then there is exactly one $p^*\in\Delta^n$ such that
--   $$G(y)\ \ge\ G(p^*)+\Big\langle \sum_{i=1}^m w_i g(p_i),\ y-p^*\Big\rangle\qquad\text{for all }y\in\Delta^n,$$
--   i.e. exactly one quasi-arithmetic pool $p^*=\bigoplus_{\mathbf g}^{i=1..m}(p_i,w_i)$.
--
--   This is the well-definedness claim following Definition 3.6: it turns "the unique $p^*$" of the definition into a theorem, and it is what makes the QA-pool hypothesis of Theorem 4.1 satisfiable.
--
--   **Formalization Note** Continuity of $G$ is the paper's standing assumption of p. 10. Subgradients are relative to $\Delta^n$ (footnote 10).
-- source:
--   Neyman & Roughgarden, From Proper Scoring Rules to Max-Min Optimal Forecast Aggregation, arXiv:2102.07081v2, p. 12, §3.2, paragraph after Remark 3.7 ('The QA-pool is well-defined, i.e. exists and is unique'), Definition 3.6

import Mathlib
import Definitions.Def_QAPooling_MaxMin_Model

namespace QAPooling.MaxMin

/-- The QA pool is well-defined (§3.2, p. 12): for forecasts in `D` with non-negative weights adding
to 1, there is exactly one `p* ∈ Δⁿ` at which `Σ_i w_i g(p_i)` is a subgradient of `G`. -/
theorem qaPool_existsUnique {n m : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hreg : IsRegular s) (hprop : IsProper s)
    (hGcont : ContinuousOn (expectedReward s) (stdSimplex ℝ (Fin n)))
    (hg : IsExposure s g)
    (p : Fin m → Fin n → ℝ) (hp : ∀ i, p i ∈ forecastDomain s)
    (w : Fin m → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    ∃! pstar, IsQAPool s g p w pstar := by sorry

end QAPooling.MaxMin

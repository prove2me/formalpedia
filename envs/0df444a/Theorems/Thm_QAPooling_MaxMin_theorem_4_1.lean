-- Prove2me | Theorems.Thm_QAPooling_MaxMin_theorem_4_1
-- name    : QAPooling.MaxMin.theorem_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:45.372603+00:00
-- url     : https://prove2.me/theorems/8968fdb9-ba2a-4f34-896f-fdff172fe8de
-- title:
--   Theorem 4.1, p. 14 — the QA pool uniquely maximizes the worst-case profit min_j u(p; j), attained at every j with p*_j > 0, non-negative and positive unless all reports agree
-- statement:
--   Let $s$ be a regular proper scoring rule on $n$ outcomes such that each $s(\cdot\,;j)$ and the expected reward $G$ are continuous on $\Delta^n$, and let $g$ be its exposure function. Fix forecasts $p_1,\dots,p_m\in\mathcal D$ with non-negative weights $w_1,\dots,w_m$ adding to $1$, and define the agent's profit
--   $$u(q;j)\;=\;s(q;j)-\sum_{i=1}^m w_i\,s(p_i;j).$$
--   Let $p^*=\bigoplus_{\mathbf g}^{i=1..m}(p_i,w_i)$ be the quasi-arithmetic pool. Then:
--
--   1. $\min_j u(q;j)$ is uniquely maximized at $q=p^*$: every report $q\in\Delta^n$ with $q\neq p^*$ has $\min_j u(q;j)<\min_j u(p^*;j)$;
--   2. the minimum over outcomes is attained simultaneously by all $j$ with $p^*_j>0$: $u(p^*;j)=\min_{j'}u(p^*;j')$ for each such $j$;
--   3. $\min_j u(p^*;j)\ge 0$;
--   4. $\min_j u(p^*;j)>0$ unless all reports $p_i$ with positive weights are equal.
--
--   Read as a contract: an agent paid by $s$ who sub-contracts $m$ experts, paying expert $i$ the amount $w_i s(p_i;j)$, guarantees itself the largest possible worst-case profit by reporting the QA pool of the experts' forecasts, and no other report guarantees as much. This is the paper's max-min justification of quasi-arithmetic pooling.
--
--   **Formalization Note** The QA pool is a hypothesis: $p^*\in\Delta^n$ with $\sum_i w_i g(p_i)$ a subgradient of $G$ at $p^*$ relative to $\Delta^n$; its existence and uniqueness is the theorem `qaPool_existsUnique`. Regularity and the two continuity assumptions are the paper's standing assumptions of pp. 9–10. Scores live in the extended reals, so $u(q;j)=-\infty$ when $s(q;j)=-\infty$; the minimum over outcomes is an infimum over the finitely many outcomes, and $n\ge 1$ follows from $p^*\in\Delta^n$. "Unless all positive-weight reports are equal" is read as: if two reports with positive weights differ, the minimum is positive.
-- source:
--   Neyman & Roughgarden, From Proper Scoring Rules to Max-Min Optimal Forecast Aggregation, arXiv:2102.07081v2, p. 14, Theorem 4.1

import Mathlib
import Definitions.Def_QAPooling_MaxMin_Model

namespace QAPooling.MaxMin

/-- Theorem 4.1 (p. 14). For a regular, proper, continuous scoring rule `s` with exposure function
`g`, forecasts `p_i ∈ D` and non-negative weights `w_i` adding to 1, let `p*` be their QA pool and
`u(q; j) = s(q; j) − Σ_i w_i s(p_i; j)`. Then:
1. every report `q ∈ Δⁿ` other than `p*` has `min_j u(q; j) < min_j u(p*; j)`;
2. `u(p*; j) = min_j u(p*; j)` for every `j` with `p*_j > 0`;
3. `min_j u(p*; j) ≥ 0`;
4. `min_j u(p*; j) > 0` unless all reports with positive weight are equal. -/
theorem theorem_4_1 {n m : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hreg : IsRegular s) (hprop : IsProper s)
    (hcont : ∀ j, ContinuousOn (fun p => s p j) (stdSimplex ℝ (Fin n)))
    (hGcont : ContinuousOn (expectedReward s) (stdSimplex ℝ (Fin n)))
    (hg : IsExposure s g)
    (p : Fin m → Fin n → ℝ) (hp : ∀ i, p i ∈ forecastDomain s)
    (w : Fin m → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (pstar : Fin n → ℝ) (hpstar : IsQAPool s g p w pstar) :
    (∀ q ∈ stdSimplex ℝ (Fin n), q ≠ pstar → minProfit s p w q < minProfit s p w pstar) ∧
    (∀ j, 0 < pstar j → profit s p w pstar j = minProfit s p w pstar) ∧
    0 ≤ minProfit s p w pstar ∧
    ((∃ i i', 0 < w i ∧ 0 < w i' ∧ p i ≠ p i') → 0 < minProfit s p w pstar) := by sorry

end QAPooling.MaxMin

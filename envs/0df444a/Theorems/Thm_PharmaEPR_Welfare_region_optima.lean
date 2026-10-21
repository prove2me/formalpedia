-- Prove2me | Theorems.Thm_PharmaEPR_Welfare_region_optima
-- name    : PharmaEPR.Welfare.region_optima
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:26.159078+00:00
-- url     : https://prove2.me/theorems/a61f87e8-1dd9-4ea9-a4af-3fc7ee5c8386
-- title:
--   Proof of Propositions 1–2, Online Appendix pp. 1–2 — producer profit in each prescription region
-- statement:
--   In the stated regime $0<\alpha<1/4$, $0<\beta<o_d/2$, $u_p\ge0$, and $\alpha+\beta\le1$, maximize producer profit separately over feasible actions that induce a need-level prescription and those that induce over-prescription. For every EC collection rate $r\in[0,1]$, the attained regional profits are
--
--   $$\Pi_m^{EC(i)*}(r)=\frac{3-6\alpha-kr+3u_p}{6},\qquad
--   \Pi_m^{EC(ii)*}(r)=1-\alpha-\beta-\frac{kr}{2}.$$
--
--   For every SR fee $t\ge0$, they are
--
--   $$\Pi_m^{SR(i)*}(t)=\frac{1-2\alpha-t+u_p}{2},\qquad
--   \Pi_m^{SR(ii)*}(t)=1-\alpha-\beta-t.$$
--
--   Region (ii) is at least as profitable as region (i) precisely when $r\le\bar r_{EC}=3(1-2\beta-u_p)/(2k)$ under EC, or $t\le\bar t=1-2\beta-u_p$ under SR. These attained regional optima and switching conditions are the quantitative inputs to the subsequent thresholds.
--
--   **Formalization Note** Region (i) is the strict no-over-prescription condition. The page's earlier region-(ii) shorthand omits $p$; the condition used here is the one in Lemma 1 and the following appendix paragraph.
-- source:
--   Alev, Atasu, Toktay & Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020-09-05 posting), Online Appendix pp. 1–2, proof of Propositions 1–2

import Mathlib
import Definitions.Def_PharmaEPR_Welfare_Model

namespace PharmaEPR.Welfare

theorem region_optima (P : Params) (hP : Regime P) :
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      IsGreatest
        {v : ℝ | ∃ a, ProdFeasible P a ∧ ¬ OverPrescribes P a ∧
          prodProfit P .EC ⟨r, 0⟩ a = v}
        ((3 - 6 * P.alpha - P.k * r + 3 * P.up) / 6) ∧
      IsGreatest
        {v : ℝ | ∃ a, ProdFeasible P a ∧ OverPrescribes P a ∧
          prodProfit P .EC ⟨r, 0⟩ a = v}
        (1 - P.alpha - P.beta - P.k * r / 2) ∧
      (1 - P.alpha - P.beta - P.k * r / 2 ≥
        (3 - 6 * P.alpha - P.k * r + 3 * P.up) / 6 ↔
        r ≤ rBarEC P)) ∧
    (∀ t : ℝ, 0 ≤ t →
      IsGreatest
        {v : ℝ | ∃ a, ProdFeasible P a ∧ ¬ OverPrescribes P a ∧
          prodProfit P .SR ⟨0, t⟩ a = v}
        ((1 - 2 * P.alpha - t + P.up) / 2) ∧
      IsGreatest
        {v : ℝ | ∃ a, ProdFeasible P a ∧ OverPrescribes P a ∧
          prodProfit P .SR ⟨0, t⟩ a = v}
        (1 - P.alpha - P.beta - t) ∧
      (1 - P.alpha - P.beta - t ≥
        (1 - 2 * P.alpha - t + P.up) / 2 ↔ t ≤ tBar P)) := by sorry

end PharmaEPR.Welfare

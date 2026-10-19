-- Prove2me | Theorems.Thm_QueueScalp_Entry_proposition_3
-- name    : QueueScalp.Entry.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:53.863417+00:00
-- url     : https://prove2.me/theorems/c06eaf5e-2a3d-48c3-8454-756ee4e4d992
-- title:
--   Proposition 3 — revenue is unimodal
-- statement:
--   For the uniform delay-cost single-scalper model, let $\Pi(\Lambda)$ be the attained maximum revenue at demand $\Lambda>0$. There is a unique turning demand $\Lambda^*\ge\mu-1/V$ such that revenue is strictly increasing for positive demands up to $\Lambda^*$ and strictly decreasing for demands above it:
--
--   $$\Lambda^*=\max\left\{\mu-\frac1V,\frac{5+\sqrt{13}}{2V}\right\}.$$
--
--   The turning point describes how congestion first raises the value of better position and, at high demand, reduces feasible sales and price.
--
--   **Formalization Note** The explicit value follows the proof's $\sqrt{1+\tilde\Lambda V}=(1+\sqrt{13})/2$. Revenue comparisons are stated through `IsOptRevenue`, so they concern the model's optimizer rather than an unrelated closed-form function.
-- source:
--   Yang, Wang & Cui, A Model of Queue-Scalping, authors' manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3865), p. 11 (PDF 11), Proposition 3; proof, Online Appendix p. 3 (PDF 36)

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model

namespace QueueScalp.Entry

theorem proposition_3 (P : Params) (hS : P.Standing) :
    (∃! LamS : ℝ,
      P.mu - 1 / P.V ≤ LamS ∧
      (∀ L₁ L₂ R₁ R₂ : ℝ, 0 < L₁ → L₁ < L₂ → L₂ ≤ LamS →
        IsOptRevenue P L₁ R₁ → IsOptRevenue P L₂ R₂ → R₁ < R₂) ∧
      (∀ L₁ L₂ R₁ R₂ : ℝ, LamS < L₁ → L₁ < L₂ →
        IsOptRevenue P L₁ R₁ → IsOptRevenue P L₂ R₂ → R₂ < R₁)) ∧
    (P.mu - 1 / P.V ≤ LamStar P ∧
      (∀ L₁ L₂ R₁ R₂ : ℝ, 0 < L₁ → L₁ < L₂ → L₂ ≤ LamStar P →
        IsOptRevenue P L₁ R₁ → IsOptRevenue P L₂ R₂ → R₁ < R₂) ∧
      (∀ L₁ L₂ R₁ R₂ : ℝ, LamStar P < L₁ → L₁ < L₂ →
        IsOptRevenue P L₁ R₁ → IsOptRevenue P L₂ R₂ → R₂ < R₁)) := by sorry
end QueueScalp.Entry

-- Prove2me | Theorems.Thm_SkillData_GoldRush_eq_C18_limit
-- name    : SkillData.GoldRush.eq_C18_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:09.408708+00:00
-- url     : https://prove2.me/theorems/ff821315-9764-43da-95d0-3ac905fe948b
-- title:
--   (C18), proof of Proposition 5, p. 39 (PDF 40) — as τη → ∞, the equilibrium λ∗ tends to a root of (C18)
-- statement:
--   Fix the parameters under the standing assumptions, an admissible cost family $C$ and a cost parameter $c>0$. There is $\bar\lambda\in(0,1)$ solving (C18),
--   $$\frac12e^{\gamma C(c,\bar\lambda)/(1-\beta)}\left(\sqrt{\frac{1}{\frac{\gamma Z_H}{\bar\lambda(Z_H+Z_L)\sqrt{\tau_\theta\tau_u}}+1}}+\sqrt{\frac{1}{\frac{\gamma Z_L}{\bar\lambda(Z_H+Z_L)\sqrt{\tau_\theta\tau_u}}+1}}\right)=1,$$
--   and the mass $\lambda^*$ of skilled investors in every equilibrium converges to $\bar\lambda$ as $\tau_\eta\to\infty$. That is, for every $\varepsilon>0$ there is $T$ such that, for all $\tau_\eta\ge T$ and every equilibrium $(x^*,\lambda^*,\alpha^*)$ at $(c,\tau_\eta)$, $|\lambda^*-\bar\lambda|<\varepsilon$.
--
--   The left-hand side of (C18) increases in $\lambda$ and in $c$. The equation therefore determines the leading-order effect of the cost parameter on the population of skilled investors.
--
--   **Formalization Note.** In (C18), $C$ stands for $C(c,\lambda)$. The paper derives (C18) by plugging its expansions into the $\tau_\eta=\infty$ form (C15) of equation (19). The rigorous content formalized here is that the exact equilibrium mass converges to a root of (C18).
-- source:
--   Huang, Xiong & Yang, Skill Acquisition and Data Sales, working paper (July 2019 version), p. 39 (PDF 40), proof of Proposition 5, equation (C18)

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model

namespace SkillData.GoldRush

theorem eq_C18_limit (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ) (hC : IsCostFamily C)
    (c : ℝ) (hc : 0 < c) :
    ∃ lb ∈ Set.Ioo (0 : ℝ) 1, EqC18 P C c lb ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ τη : ℝ, T ≤ τη →
        ∀ (X : Clarity) (lam α : ℝ), IsEquilibrium P C c τη X lam α → |lam - lb| < ε := by sorry

end SkillData.GoldRush

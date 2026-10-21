-- Prove2me | Theorems.Thm_SkillData_GoldRush_proposition_1
-- name    : SkillData.GoldRush.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:27.836917+00:00
-- url     : https://prove2.me/theorems/fe92978b-f4fd-4a94-b4b7-87393eccaec2
-- title:
--   Proposition 1, p. 14 (PDF 15) — α is the unique positive root of (14)
-- statement:
--   Fix the parameters under the standing assumptions, a data accuracy $\tau_\eta>0$, a finite clarity $x>0$ and a mass of skilled investors $\lambda\in(0,1]$. Then equation (14),
--   $$\gamma\alpha\big(xZ_H+\tau_u\alpha^2+\tau_\eta\big)-\tfrac12 x\lambda\tau_\eta\Big(Z_H+Z_L+\frac{xZ_L(Z_H-Z_L)}{xZ_L+\tau_u\alpha^2+\tau_\eta}\Big)=0,$$
--   has exactly one positive real root $\alpha$.
--
--   The root $\alpha=a_\theta/a_u$ characterizes the financial-market equilibrium at the given $(\lambda,x)$. It is the price-signal precision that enters price informativeness.
--
--   **Formalization Note.** Only the root statement is formalized. The existence and uniqueness of a linear price function (4) belong to the CARA-normal derivation, which the mission takes as given. The page's "given $(\lambda,x)$" is read as $\lambda\in(0,1]$ and $x\in(0,\infty)$: at $\lambda=0$ or $x=0$ the only nonnegative root is $\alpha=0$, and $x=\infty$ is handled separately by the definitions.
-- source:
--   Huang, Xiong & Yang, Skill Acquisition and Data Sales, working paper (July 2019 version), p. 14 (PDF 15), Proposition 1, equation (14)

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model

namespace SkillData.GoldRush

theorem proposition_1 (P : Params) (hP : P.Standing) (τη x lam : ℝ) (hτη : 0 < τη)
    (hx : 0 < x) (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    ∃! α : ℝ, 0 < α ∧ Eq14 P τη x lam α := by sorry

end SkillData.GoldRush

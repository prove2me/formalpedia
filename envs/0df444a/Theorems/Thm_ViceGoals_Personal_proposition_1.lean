-- Prove2me | Theorems.Thm_ViceGoals_Personal_proposition_1
-- name    : ViceGoals.Personal.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:30.556298+00:00
-- url     : https://prove2.me/theorems/5c700055-a7e1-4a61-805f-b85623bca47a
-- title:
--   Proposition 1: personal goals reverse the price effect at h1
-- statement:
--   Consider the benchmark monopoly and the monopoly facing consumers who set personal goals. Assume $v>0$, $0<\beta<1$, $\lambda>0$, and $0<h<v/(2-\beta)$. Each regime has an equilibrium price. For every benchmark equilibrium price $p^B$ and personal-goal equilibrium price $p^*$, with
--
--   $$h_1=\frac{v(1+2\lambda)}{4-3\beta+6\lambda-4\beta\lambda},$$
--
--   the comparison is
--
--   $$h>h_1\implies p^*>p^B,\qquad 0<h<h_1\implies p^*<p^B.$$
--
--   The theorem formalizes the paper's central price comparison, including existence of both prices.
--
--   **Formalization Note** The section assumes $h\le v/(2-\beta)$. The right endpoint is excluded because the benchmark profit is then zero at every nonnegative price, so its equilibrium price is not unique. Demand comes from the nested consumer optimization problems, not from a stipulated closed form.
-- source:
--   Amaldoss & Harutyunyan, Pricing of Vice Goods for Goal-Driven Consumers, SSRN 4226237 (version of September 2022), p. 14 (PDF 15), §4.2, Proposition 1

import Mathlib
import Definitions.Def_ViceGoals_Personal_Model

namespace ViceGoals.Personal

theorem proposition_1 (m : Params) (hm : m.Standing) (hh : 0 < m.h)
    (hhmax : m.h < m.v / (2 - m.beta)) :
    (∃ p, IsEqPriceB m p) ∧ (∃ p, IsEqPriceGoal m p) ∧
    ∀ pB pS : ℝ, IsEqPriceB m pB → IsEqPriceGoal m pS →
      (h1 m < m.h → pB < pS) ∧ (m.h < h1 m → pS < pB) := by sorry

end ViceGoals.Personal

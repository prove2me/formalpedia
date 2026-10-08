-- Prove2me | Theorems.Thm_TaoAnDCA_TRS_theorem_3_7_iii
-- name    : TaoAnDCA.TRS.theorem_3_7_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:45.222179+00:00
-- url     : https://prove2.me/theorems/c49251c2-2d41-42b3-92c8-bd9ebb579237
-- title:
--   Theorem 3.7(iii), p. 488 — if α is finite, both DCA objectives decrease to a common limit β ≥ α and the steps vanish
-- statement:
--   Let $g,h$, the simplified DCA sequences $\{x^k\}$, $\{y^k\}$ and the constants $\rho_1,\rho_2,\rho_1^*,\rho_2^*$ be as in Theorem 3.7(i), and suppose that the optimal value $\alpha = \inf_x\{g(x)-h(x)\}$ is finite. Then there is a real number $\beta\ge\alpha$ such that
--   1. the sequences $\{(g-h)(x^k)\}$ and $\{(h^*-g^*)(y^k)\}$ are decreasing and
--   $$\lim_{k\to+\infty}(g-h)(x^k) = \lim_{k\to+\infty}(h^*-g^*)(y^k) = \beta;$$
--   2. if $\rho_1+\rho_2>0$ then $\lim_{k\to+\infty}(x^{k+1}-x^k) = 0$, and if $\rho_1^*+\rho_2^*>0$ then $\lim_{k\to+\infty}(y^{k+1}-y^k) = 0$;
--   3. $$\lim_{k\to+\infty}\{g(x^k)+g^*(y^k)-\langle x^k,y^k\rangle\} = 0 = \lim_{k\to+\infty}\{h(x^{k+1})+h^*(y^k)-\langle x^{k+1},y^k\rangle\}.$$
--
--   Item 3 says the Fenchel–Young gaps of the two pairs vanish asymptotically, which is the step from descent to criticality of the limit points.
--
--   **Formalization Note.** The paper's hypothesis "$\rho(g)+\rho(h)>0$" is stated as $\rho_1+\rho_2>0$ for the chosen constants: when the moduli have a positive sum, admissible constants with a positive sum exist, and conversely. "$\alpha$ finite" is $\alpha\ne-\infty$; $\alpha<+\infty$ always holds because $g$ is proper and $\operatorname{dom}g\subset\operatorname{dom}h$. Item 3 is written in `EReal`; along a run all the terms are finite.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 488, §3.4, Theorem 3.7(iii)

import Mathlib
import Definitions.Def_TaoAnDCA_TRS_Setting

open Filter Topology

namespace TaoAnDCA.TRS

theorem theorem_3_7_iii {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (hgh : TaoAnDCA.GlobalOpt.DCStanding g h)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsSimplifiedDCARun g h x y)
    (ρ₁ ρ₂ ρ₁' ρ₂' : ℝ) (h₁ : IsRhoConvex g ρ₁) (h₂ : IsRhoConvex h ρ₂)
    (h₁' : IsRhoConvex (CondatPD.FinDim.conj g) ρ₁') (h₂' : IsRhoConvex (CondatPD.FinDim.conj h) ρ₂')
    (hα : TaoAnDCA.GlobalOpt.primalValue g h ≠ ⊥) :
    ∃ β : ℝ, TaoAnDCA.GlobalOpt.primalValue g h ≤ (β : EReal) ∧
      Antitone (fun k => TaoAnDCA.GlobalOpt.dcSub g h (x k)) ∧
      Antitone (fun k => TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) (y k)) ∧
      Tendsto (fun k => TaoAnDCA.GlobalOpt.dcSub g h (x k)) atTop (𝓝 (β : EReal)) ∧
      Tendsto (fun k => TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) (y k)) atTop
        (𝓝 (β : EReal)) ∧
      (0 < ρ₁ + ρ₂ → Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0)) ∧
      (0 < ρ₁' + ρ₂' → Tendsto (fun k => y (k + 1) - y k) atTop (𝓝 0)) ∧
      Tendsto (fun k => g (x k) + CondatPD.FinDim.conj g (y k) -
        ((inner ℝ (x k) (y k) : ℝ) : EReal)) atTop (𝓝 0) ∧
      Tendsto (fun k => h (x (k + 1)) + CondatPD.FinDim.conj h (y k) -
        ((inner ℝ (x (k + 1)) (y k) : ℝ) : EReal)) atTop (𝓝 0) := by sorry

end TaoAnDCA.TRS

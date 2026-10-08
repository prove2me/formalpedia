-- Prove2me | Theorems.Thm_TaoAnDCA_TRS_corollary_A_2
-- name    : TaoAnDCA.TRS.corollary_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:00.367089+00:00
-- url     : https://prove2.me/theorems/4a33b30a-5537-4915-a63d-fc646f46ee86
-- title:
--   Corollary A.2(i)–(ii), p. 501 — the primal descent of the DCA with the dual decrements ρ₁*/2‖dy^{k−1}‖², ρ₂*/2‖dy^k‖²
-- statement:
--   Let $g,h$ and the simplified DCA sequences $\{x^k\}$, $\{y^k\}$ be as in Proposition A.1, and let $\rho_1,\rho_2,\rho_1^*,\rho_2^*\ge 0$ be constants such that $g$, $h$, $g^*$, $h^*$ are respectively $\rho_1$-, $\rho_2$-, $\rho_1^*$- and $\rho_2^*$-convex. Write $dx^k = x^{k+1}-x^k$ and $dy^k = y^{k+1}-y^k$. Then for every $k\ge1$:
--   1. $$(g-h)(x^{k+1})\le(h^*-g^*)(y^k)-\frac{\rho_2}{2}\|dx^k\|^2\le(g-h)(x^k)-\Big[\frac{\rho_1^*}{2}\|dy^{k-1}\|^2+\frac{\rho_2}{2}\|dx^k\|^2\Big];$$
--   2. $$(g-h)(x^{k+1})\le(h^*-g^*)(y^k)-\frac{\rho_2^*}{2}\|dy^k\|^2\le(g-h)(x^k)-\Big[\frac{\rho_1^*}{2}\|dy^{k-1}\|^2+\frac{\rho_2^*}{2}\|dy^k\|^2\Big];$$
--   3. $(g-h)(x^{k+1}) = (g-h)(x^k)$ holds if and only if $x^k\in\partial g^*(y^k)$, $y^k\in\partial h(x^{k+1})$ and $(\rho_1+\rho_2)dx^k = \rho_1^*dy^{k-1} = \rho_2^*dy^k = 0$.
--
--   Together with Proposition A.1 these inequalities give the three-term maximum in Theorem 3.7(i).
--
--   **Formalization Note.** The statement is for $k\ge1$ because $dy^{k-1}$ involves $y^{k-1}$; the natural-number subtraction `k - 1` occurs only under the hypothesis `1 ≤ k`. The dual inequalities (iii)–(iv) of the corollary are not included. Values use the convention $+\infty-(+\infty)=+\infty$ (`dcSub`).
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 501, Appendix, Corollary A.2(i)–(ii) and the first equality statement

import Mathlib
import Definitions.Def_TaoAnDCA_TRS_Setting

open Filter Topology

namespace TaoAnDCA.TRS

theorem corollary_A_2 {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (hgh : TaoAnDCA.GlobalOpt.DCStanding g h)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsSimplifiedDCARun g h x y)
    (ρ₁ ρ₂ ρ₁' ρ₂' : ℝ) (h₁ : IsRhoConvex g ρ₁) (h₂ : IsRhoConvex h ρ₂)
    (h₁' : IsRhoConvex (CondatPD.FinDim.conj g) ρ₁') (h₂' : IsRhoConvex (CondatPD.FinDim.conj h) ρ₂') :
    ∀ k : ℕ, 1 ≤ k →
      (TaoAnDCA.GlobalOpt.dcSub g h (x (k + 1)) ≤
          TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) (y k) -
            ((ρ₂ / 2 * ‖x (k + 1) - x k‖ ^ 2 : ℝ) : EReal) ∧
        TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) (y k) -
            ((ρ₂ / 2 * ‖x (k + 1) - x k‖ ^ 2 : ℝ) : EReal) ≤
          TaoAnDCA.GlobalOpt.dcSub g h (x k) -
            ((ρ₁' / 2 * ‖y k - y (k - 1)‖ ^ 2 + ρ₂ / 2 * ‖x (k + 1) - x k‖ ^ 2 : ℝ) : EReal)) ∧
      (TaoAnDCA.GlobalOpt.dcSub g h (x (k + 1)) ≤
          TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) (y k) -
            ((ρ₂' / 2 * ‖y (k + 1) - y k‖ ^ 2 : ℝ) : EReal) ∧
        TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) (y k) -
            ((ρ₂' / 2 * ‖y (k + 1) - y k‖ ^ 2 : ℝ) : EReal) ≤
          TaoAnDCA.GlobalOpt.dcSub g h (x k) -
            ((ρ₁' / 2 * ‖y k - y (k - 1)‖ ^ 2 + ρ₂' / 2 * ‖y (k + 1) - y k‖ ^ 2 : ℝ) : EReal)) ∧
      (TaoAnDCA.GlobalOpt.dcSub g h (x (k + 1)) = TaoAnDCA.GlobalOpt.dcSub g h (x k) ↔
        (x k ∈ TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) (y k) ∧ y k ∈ TaoAnDCA.GlobalOpt.subdiff h (x (k + 1)) ∧
          (ρ₁ + ρ₂) • (x (k + 1) - x k) = 0 ∧ ρ₁' • (y k - y (k - 1)) = 0 ∧
          ρ₂' • (y (k + 1) - y k) = 0)) := by sorry

end TaoAnDCA.TRS

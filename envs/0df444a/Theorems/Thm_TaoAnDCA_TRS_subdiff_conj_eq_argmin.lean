-- Prove2me | Theorems.Thm_TaoAnDCA_TRS_subdiff_conj_eq_argmin
-- name    : TaoAnDCA.TRS.subdiff_conj_eq_argmin
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:47.354974+00:00
-- url     : https://prove2.me/theorems/42387659-4e5f-40e1-bf65-7209b2072820
-- title:
--   (P_k), §3.3, p. 487 — ∂g*(y) is the set of minimizers of g − ⟨·, y⟩
-- statement:
--   Let $g\in\Gamma_0(\mathbb R^n)$ and $y\in\mathbb R^n$. Then the subdifferential of the conjugate $g^*$ at $y$ is the set of minimizers of $g$ tilted by $y$:
--   $$\partial g^*(y) = \operatorname{argmin}\{g(x) - \langle x, y\rangle : x\in\mathbb R^n\},$$
--   where only points with $g(x) < +\infty$ count as minimizers.
--
--   In the DCA, applied with $y = y^k\in\partial h(x^k)$, this is the identification (P_k): the step $x^{k+1}\in\partial g^*(y^k)$ amounts to solving the convex program obtained from (P) by replacing $h$ with its affine minorization $h(x^k) + \langle x - x^k, y^k\rangle$.
--
--   **Formalization Note.** The paper writes the objective as $g(x) - [h(x^k) + \langle x - x^k, y^k\rangle]$; it differs from $g(x) - \langle x, y^k\rangle$ by the constant $h(x^k) - \langle x^k, y^k\rangle$, which does not change the set of minimizers, so the statement is given in this general form. The minimizers are required to lie in $\operatorname{dom} g$, as the subdifferential is empty off $\operatorname{dom} g^*$ and a minimizer of a proper function has a finite value.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 487, §3.3, display (P_k)

import Mathlib
import Definitions.Def_TaoAnDCA_TRS_Setting

open Filter Topology

namespace TaoAnDCA.TRS

theorem subdiff_conj_eq_argmin {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g) (y : EuclideanSpace ℝ (Fin n)) :
    TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) y =
      {x | g x ≠ ⊤ ∧ ∀ z, g x - ((inner ℝ x y : ℝ) : EReal) ≤ g z - ((inner ℝ z y : ℝ) : EReal)} := by sorry

end TaoAnDCA.TRS

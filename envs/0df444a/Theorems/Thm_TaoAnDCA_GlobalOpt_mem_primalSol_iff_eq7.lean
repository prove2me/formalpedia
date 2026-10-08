-- Prove2me | Theorems.Thm_TaoAnDCA_GlobalOpt_mem_primalSol_iff_eq7
-- name    : TaoAnDCA.GlobalOpt.mem_primalSol_iff_eq7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:18.119582+00:00
-- url     : https://prove2.me/theorems/d7033c46-3bf6-4543-8e67-d20293255a21
-- title:
--   §3.1, proof of Theorem 3.1, (6)–(7), p. 483 — x* ∈ 𝒫 iff x* ∈ dom g and g(x*) + g*(y) ≤ h(x*) + h*(y) for all y ∈ dom h*
-- statement:
--   Let $g,h\in\Gamma_0(\mathbb R^n)$ satisfy the standing inclusions (3), with the convention $+\infty-(+\infty)=+\infty$, and let $\mathcal P$ be the solution set of the d.c. program $\alpha=\inf\{g(x)-h(x)\}$. For every $x^*\in\mathbb R^n$ the following are equivalent:
--
--   1. $x^*\in\mathcal P$;
--   2. $x^*\in\operatorname{dom}g$ and
--   $$g(x^*)-h(x^*)\le h^*(y)-g^*(y)\qquad\forall y\in\operatorname{dom}h^*;\tag{6}$$
--   3. $x^*\in\operatorname{dom}g$ and
--   $$g(x^*)+g^*(y)\le h(x^*)+h^*(y)\qquad\forall y\in\operatorname{dom}h^*.\tag{7}$$
--
--   By d.c. duality, $x^*$ is optimal exactly when its value does not exceed any value of the dual objective; (7) is the same inequality with the terms rearranged. This is the first half of the proof of Theorem 3.1(i).
--
--   **Formalization Note** The statement is the conjunction of "1 iff 2" and "1 iff 3". In (6) the differences are the convention-respecting `dcSub`; in (7) the sums are taken in the extended reals. On the ranges involved all four terms are finite: $g(x^*)$ and $h(x^*)$ because $x^*\in\operatorname{dom}g\subset\operatorname{dom}h$ and $h$ is proper, $h^*(y)$ because $y\in\operatorname{dom}h^*$, and $g^*(y)$ because $\operatorname{dom}h^*\subset\operatorname{dom}g^*$ and $g$ is proper. The restriction $y\in\operatorname{dom}h^*$ is kept as on the page.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 483, §3.1, proof of Theorem 3.1, displays (6) and (7)

import Mathlib
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting

open TaoAnDCA.GlobalOpt

namespace TaoAnDCA.GlobalOpt

theorem mem_primalSol_iff_eq7 {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : DCStanding g h) (x : EuclideanSpace ℝ (Fin n)) :
    (x ∈ primalSol g h ↔ x ∈ effDom g ∧
      ∀ y ∈ effDom (CondatPD.FinDim.conj h),
        dcSub g h x ≤ dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y) ∧
    (x ∈ primalSol g h ↔ x ∈ effDom g ∧
      ∀ y ∈ effDom (CondatPD.FinDim.conj h),
        g x + CondatPD.FinDim.conj g y ≤ h x + CondatPD.FinDim.conj h y) := by sorry

end TaoAnDCA.GlobalOpt

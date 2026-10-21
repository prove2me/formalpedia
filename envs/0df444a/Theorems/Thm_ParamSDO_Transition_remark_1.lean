-- Prove2me | Theorems.Thm_ParamSDO_Transition_remark_1
-- name    : ParamSDO.Transition.remark_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:06.323306+00:00
-- url     : https://prove2.me/theorems/e8b0d93f-9644-48ab-ad2c-6165efc8fa66
-- title:
--   Remark 1, p. 2 — strictly feasible primal and dual solutions exist at every ϵ ∈ int(𝓔)
-- statement:
--   Consider the parametric semidefinite pair $(\mathrm P_\epsilon)/(\mathrm D_\epsilon)$ with symmetric data $A^1,\dots,A^m,C,\bar C\in\mathbb S^n$ and $b\in\mathbb R^m$, primal feasible set $\mathcal P$, dual feasible sets $\mathcal D(\epsilon)$ and domain $\mathcal E=\{\epsilon:\ v(\epsilon)>-\infty\}$ of the optimal value function. Suppose the $A^i$ are linearly independent (Assumption 1) and the interior point condition holds at $\epsilon=0$ (Assumption 2). Then for every $\epsilon\in\operatorname{int}(\mathcal E)$ there are
--   $$
--   X^\circ\in\mathcal P\ \text{with}\ X^\circ\succ0\qquad\text{and}\qquad (y^\circ,S^\circ)\in\mathcal D(\epsilon)\ \text{with}\ S^\circ\succ0 .
--   $$
--
--   The interior point condition is assumed only at $\epsilon=0$; this remark propagates it to the whole interior of the domain, which is what makes strong duality available at every $\epsilon\in\operatorname{int}(\mathcal E)$.
--
--   **Formalization Note** The primal feasible set does not depend on $\epsilon$. The symmetry of the data and Assumptions 1–2 are the paper's standing assumptions and are carried as hypotheses.
-- source:
--   Hauenstein, Mohammad-Nezhad, Tang & Terlaky, On computing the nonlinearity interval in parametric semidefinite optimization, arXiv:1908.10499v3, p. 2, Remark 1

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting

namespace ParamSDO.Transition

theorem remark_1 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    ∀ ϵ ∈ interior (domE A b C Cbar),
      (∃ X ∈ Pfeas A b, X.PosDef) ∧ ∃ p ∈ Dfeas A C Cbar ϵ, p.2.PosDef := by sorry

end ParamSDO.Transition

-- Prove2me | Theorems.Thm_RobustUncLP_WorstCase_proposition_2_1
-- name    : RobustUncLP.WorstCase.proposition_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:52:35.012588+00:00
-- url     : https://prove2.me/theorems/41c83196-2b8d-4cf0-87d1-dbc8a1ef2617
-- title:
--   Proposition 2.1, p. 5 — under constraint-wise uncertainty and boundedness, (P_𝒰) is infeasible iff some instance is, and c* = sup c*(P)
-- statement:
--   Consider the uncertain linear program $\min\{c^{T}x \mid Ax\ge 0,\ f^{T}x = 1\}$ with fixed $c, f\in\mathbb R^n$ and uncertain $m\times n$ matrix $A$ ranging over a nonempty, convex and closed uncertainty set $\mathcal U$. Its robust counterpart is
--   $$(P_{\mathcal U})\qquad \min\{c^{T}x \mid x\in G_{\mathcal U}\},\qquad G_{\mathcal U} = \{x \mid Ax\ge0\ \forall A\in\mathcal U;\ f^{T}x = 1\},$$
--   and for $A\in\mathcal U$ the instance $(P)$ has feasible set $\{x\mid Ax\ge0,\ f^{T}x = 1\}$ and optimal value $c^*(P)$.
--
--   Assume the uncertainty is **constraint-wise**, $\mathcal U = \mathcal U_1\times\dots\times\mathcal U_m$ with $\mathcal U_i$ the set of $i$-th rows of matrices in $\mathcal U$, and the **Boundedness Assumption** holds: some convex compact $Q\subseteq\mathbb R^n$ contains the feasible sets of all instances. Then:
--
--   1. $(P_{\mathcal U})$ is infeasible if and only if there exists an infeasible instance.
--   2. If $(P_{\mathcal U})$ is feasible and $c^*$ is its optimal value (the infimum of $c^{T}x$ over $G_{\mathcal U}$), then
--   $$c^* = \sup\{c^*(P) \mid (P)\in\mathcal P\}. \tag{9}$$
--
--   The robust counterpart is thus no worse than the worst instance: neither its feasibility nor its optimal value is more conservative than the worst realization of the data. The §2.2 example shows that without constraint-wise uncertainty this can fail.
--
--   **Formalization Note** Optimal values are infima: $c^*$ is the greatest lower bound of $\{c^{T}x \mid x\in G_{\mathcal U}\}$ (`IsGLB`), and (9) says $c^*$ is the least upper bound (`IsLUB`) of the set of reals $v$ that are the optimal value of some instance $A\in\mathcal U$ (instances without a real optimal value contribute nothing; under the hypotheses of (ii) there are none). Convexity and closedness of $\mathcal U$ are the standing assumption of §2.1. Nonemptiness of $\mathcal U$ is added: the paper takes it for granted, and without it (i) fails for $f = 0$ and the supremum in (9) is over the empty set.
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, p. 5, Proposition 2.1 and (9); standing assumption §2.1, p. 3; Boundedness Assumption p. 4

import Mathlib
import Definitions.Def_RobustUncLP_WorstCase_Setting
open Matrix

namespace RobustUncLP.WorstCase

theorem proposition_2_1 {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ))
    (c f : Fin n → ℝ)
    (hconv : Convex ℝ U) (hclosed : IsClosed U) (hne : U.Nonempty)
    (hcw : IsConstraintWise U) (hbdd : BoundednessAssumption U f) :
    (robustFeas U f = ∅ ↔ ∃ A ∈ U, instFeas f A = ∅) ∧
    ∀ cstar : ℝ, (robustFeas U f).Nonempty →
      IsGLB ((fun x => c ⬝ᵥ x) '' robustFeas U f) cstar →
      IsLUB {v : ℝ | ∃ A ∈ U, IsGLB ((fun x => c ⬝ᵥ x) '' instFeas f A) v} cstar := by sorry

end RobustUncLP.WorstCase

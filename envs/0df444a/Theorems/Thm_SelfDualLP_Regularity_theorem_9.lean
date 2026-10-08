-- Prove2me | Theorems.Thm_SelfDualLP_Regularity_theorem_9
-- name    : SelfDualLP.Regularity.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:12.6417+00:00
-- url     : https://prove2.me/theorems/65b329c5-a515-4cb9-a065-fb15f381fb8d
-- title:
--   Theorem 9: interior feasibility makes τ positive at every HLP optimum
-- statement:
--   Suppose the primal and dual programs both have interior feasible points: some $x^+\in\mathbb R^n$ satisfies $Ax^+=b$ and $x^+_j>0$ for every $j$, and some $y^+\in\mathbb R^m$ has strictly positive slack $c-A^Ty^+$. Under the paper's initial choice $y^0=0$ and $x^0=s^0=e$, every self-complementary solution $(y^*,x^*,\tau^*,\theta^*,s^*,\kappa^*)$ of (HLP) satisfies
--   $$
--   \tau^*>0.
--   $$
--   A self-complementary solution means any optimal solution of (HLP), with no strict complementarity requirement. Theorem 2(iv) entails $\theta^*=0$; it is not separately assumed. Existence of an interior feasible point already implies ordinary feasibility for each original program.
--
--   The result ensures that an arbitrary HLP optimum can be rescaled to give primal and dual optimal solutions when both original programs satisfy this regularity assumption.
--
--   **Formalization Note** Interior means strict coordinatewise feasibility, not topological interior of an equality-constrained set. The statement permits $m=0$ or $n=0$, with the usual empty-coordinate convention.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 64, Theorem 9; DOI 10.1287/moor.19.1.53

import Definitions.Def_SelfDualLP_Regularity_HLP

namespace SelfDualLP.Regularity

/-- Ye--Todd--Mizuno (1994), Theorem 9, p. 64. The interior here is
coordinatewise strict feasibility, not topological interior in ambient space. -/
theorem theorem_9 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hP : ∃ x, PrimalInterior A b x)
    (hD : ∃ y, DualInterior A c y)
    (w : HLPPoint m n) (hw : IsSelfComplementary A b c w) :
    0 < w.τ := by sorry

end SelfDualLP.Regularity

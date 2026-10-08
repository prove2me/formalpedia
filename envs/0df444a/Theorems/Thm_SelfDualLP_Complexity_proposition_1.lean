-- Prove2me | Theorems.Thm_SelfDualLP_Complexity_proposition_1
-- name    : SelfDualLP.Complexity.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:01.799012+00:00
-- url     : https://prove2.me/theorems/10a4624f-36a7-4b95-9a05-574930796665
-- title:
--   Proposition 1 — a skew-symmetric program is self-dual and, if feasible, has optimal value zero
-- statement:
--   Let $\tilde A\in\mathbb R^{p\times p}$ be skew-symmetric ($\tilde A^T=-\tilde A$) and let $\tilde b=-\tilde c\in\mathbb R^p$. Consider
--   $$
--   \text{(SDP)}\qquad \min\ \tilde c^T\tilde u\quad\text{s.t.}\quad \tilde A\tilde u\ge\tilde b,\ \ \tilde u\ge0,
--   $$
--   whose linear-programming dual is $\max\ \tilde b^Tv$ s.t. $\tilde A^Tv\le\tilde c$, $v\ge0$. Then:
--
--   1. (SDP) is equivalent to its dual: the dual has exactly the feasible set of (SDP), and its objective is $\tilde b^Tv=-\tilde c^Tv$, so maximizing it is minimizing $\tilde c^Tv$;
--   2. every feasible $\tilde u$ of (SDP) is feasible in the dual, and the two objective values $\tilde c^T\tilde u$ and $\tilde b^T\tilde u$ sum to zero;
--   3. if (SDP) has a feasible solution, then it has an optimal solution, and its optimal value is zero.
--
--   This is the self-duality principle behind the homogeneous program (HLP), whose constraint matrix is skew-symmetric.
--
--   **Formalization Note** "Equivalent to its dual" is stated as: the two feasible sets coincide and the dual objective is the negative of the primal one. The optimal solution in part 3 is a feasible $\tilde u$ with $\tilde c^T\tilde u=0$ and $\tilde c^T\tilde u\le\tilde c^T\tilde u'$ for every feasible $\tilde u'$.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 55, Proposition 1

import Mathlib

open Matrix

namespace SelfDualLP.Complexity

/-- Proposition 1 (Ye–Todd–Mizuno 1994, p. 55). Let `Ã ∈ ℝ^{p×p}` be skew-symmetric and
`b̃ = −c̃`. Consider (SDP) `minimize c̃ᵀũ subject to Ãũ ≥ b̃, ũ ≥ 0`, whose LP dual is
`maximize b̃ᵀv subject to Ãᵀv ≤ c̃, v ≥ 0`. Then (a) the dual has exactly the same feasible set
as (SDP), and its objective `b̃ᵀv = −c̃ᵀv`, so maximizing it is minimizing `c̃ᵀv` (the dual is
(SDP) itself); (b) every feasible `ũ` is dual feasible and the two objective values
`c̃ᵀũ + b̃ᵀũ` sum to zero; (c) if (SDP) is feasible, it has an optimal solution and its
optimal value is zero. -/
theorem proposition_1 {p : ℕ} (At : Matrix (Fin p) (Fin p) ℝ) (bt ct : Fin p → ℝ)
    (hskew : Atᵀ = -At) (hbc : bt = -ct) :
    (∀ u : Fin p → ℝ,
        ((∀ i, bt i ≤ (At *ᵥ u) i) ∧ ∀ i, 0 ≤ u i) ↔
          ((∀ i, (Atᵀ *ᵥ u) i ≤ ct i) ∧ ∀ i, 0 ≤ u i)) ∧
    (∀ u : Fin p → ℝ, bt ⬝ᵥ u = -(ct ⬝ᵥ u)) ∧
    (∀ u : Fin p → ℝ, ((∀ i, bt i ≤ (At *ᵥ u) i) ∧ ∀ i, 0 ≤ u i) →
        ((∀ i, (Atᵀ *ᵥ u) i ≤ ct i) ∧ ∀ i, 0 ≤ u i) ∧ ct ⬝ᵥ u + bt ⬝ᵥ u = 0) ∧
    ((∃ u : Fin p → ℝ, (∀ i, bt i ≤ (At *ᵥ u) i) ∧ ∀ i, 0 ≤ u i) →
      ∃ u : Fin p → ℝ, ((∀ i, bt i ≤ (At *ᵥ u) i) ∧ ∀ i, 0 ≤ u i) ∧ ct ⬝ᵥ u = 0 ∧
        ∀ u' : Fin p → ℝ, ((∀ i, bt i ≤ (At *ᵥ u') i) ∧ ∀ i, 0 ≤ u' i) →
          ct ⬝ᵥ u ≤ ct ⬝ᵥ u') := by sorry

end SelfDualLP.Complexity

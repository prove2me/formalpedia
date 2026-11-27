-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_Supplement_theorem_3_5
-- name    : RobustInventory.SingleStation.Supplement.theorem_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T19:29:07.955805+00:00
-- url     : https://prove2.me/theorems/d600554c-c155-4dd2-8066-e53b9eea6b85
-- title:
--   Theorem 3.5, p. 156: with inventory capacity, the robust policy is the nominal policy for $w'$ and capacities $C-\frac{2p}{p+h}A_k$
-- statement:
--   **Theorem 3.5 (Optimal Robust Policy).** Consider the single-station model of §3.1 and suppose that stock can only be stored up to an amount $C$, the initial stock included: $x_0\le C$. The capacitated robust problem is formulation (14) with
--   $$\bar x_{k+1}+q_k\Gamma_k+\sum_{i=0}^{k}r_{ik}\le C\qquad(k<T)$$
--   on the same variables $q,r$. Let $A_k$ be the value of LP (13), $A_{-1}=0$, $w'_k=\bar w_k+\frac{p-h}{p+h}(A_k-A_{k-1})$, and $x'_{k+1}=x_0+\sum_{i=0}^{k}(u_i-w'_i)$.
--
--   An order sequence $u$ is the order part of an optimal solution of the capacitated robust problem if and only if it minimizes the nominal cost under $w'$, $\sum_{k<T}[K\mathbf 1_{\{u_k>0\}}+cu_k+\max(hx'_{k+1},-px'_{k+1})]$, over $u\ge0$ subject to inventory capacity $C$ at time $0$ and
--   $$x'_{k+1}\le C-\frac{2p}{p+h}A_k\qquad(k<T).$$
--
--   An inventory capacity thus becomes a time-varying, deterministic capacity in the modified problem.
--
--   **Formalization Note** The capacity is the variable `Cap`, since `Model.C` is the purchasing cost. Neither problem is assumed feasible; if they are infeasible, both sides of the equivalence are false. The statement does not use Lemma 3.4, which is false in general.
--
--   Differences from the source:
--   - reading: "stock can only be stored up to an amount C", with "inventory capacity at time 0 equal to C" → the hypothesis x_0 ≤ C, repeated as the time-0 constraint of the nominal problem; reason: the capacity applies to the stock held at time 0; with x_0 > C the robust problem could be feasible while the stated nominal problem is not
--   - reading: (26), "where q_k and r_ik are defined in (14)" → (26) on the same variables q, r as the cost constraints of (14), minimized jointly; reason: this is (14) with the added constraint, as §3.2.2 says
--   - reading: A_k = q*_kΓ_k + Σ r*_ik for the optimal q*, r* of (14) → A_k is the optimal value of LP (13); reason: the optimal q*, r* need not be unique (h = 0), and Remark 1 after Theorem 3.2 defines A_k by (13); the published base items use the same reading
--   - encoding: binary variables v_k with 0 ≤ u_k ≤ M v_k, M a large number → the fixed-cost indicator K·1{u_k > 0} of (21); reason: the two agree for M large enough; this is the convention of the published definitions
--   - encoding: the capacity C → a real variable named Cap; reason: Model.C already names the purchasing cost
--   - generalization: the demand is always nonnegative, ŵ_k ≤ w̄_k (p. 156) → no sign condition on w̄ or w′; reason: the statement holds without it, and nonnegative demand is a special case
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 156 (PDF 7), §3.2.2, Theorem 3.5 and Eqs. (25)–(27)

import Definitions.Def_RobustInventory_SingleStation_Supplement_InventoryCap

namespace RobustInventory.SingleStation.Supplement

/-- Theorem 3.5, p. 156: when stock can only be stored up to `Cap` (time `0` included), an order
sequence is the order part of an optimal solution of (14) with (26) iff it is optimal for the
nominal problem with demand `w'`, capacity `Cap` at time `0` and `Cap - (2p/(p+h)) A_k` at
time `k + 1`. -/
theorem theorem_3_5 (M : Model) (Cap : ℝ) (hx0 : M.x0 ≤ Cap) (u : ℕ → ℝ) :
    (∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), IsRobustCapOptimal M Cap u y q r) ↔
      IsNominalCapOptimal M Cap u := by sorry

end RobustInventory.SingleStation.Supplement

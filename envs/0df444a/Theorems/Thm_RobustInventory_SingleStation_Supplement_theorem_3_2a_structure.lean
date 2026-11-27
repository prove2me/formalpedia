-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_Supplement_theorem_3_2a_structure
-- name    : RobustInventory.SingleStation.Supplement.theorem_3_2a_structure
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T19:26:56.821061+00:00
-- url     : https://prove2.me/theorems/b61162dc-1034-41ca-8da0-d1c85fb347e9
-- title:
--   Theorem 3.2(a), last sentence, p. 155: the optimal robust policy is $(s,S)$ on the modified stock, and $(S,S)$ without fixed cost
-- statement:
--   **Theorem 3.2(a), last sentence.** Consider the single-station model of §3.1 with horizon $T$, fixed cost $K\ge0$, unit costs $c>0$, $h\ge0$, $p>c$, nominal demands $\bar w_k$, deviations $\hat w_k\ge0$ and budgets $\Gamma_k$. Let $A_k$ be the value of LP (13), $A_{-1}=0$, and
--   $$w'_k=\bar w_k+\frac{p-h}{p+h}(A_k-A_{k-1})$$
--   the modified demand (20). Then there are threshold sequences $s$, $S$, chosen independently of any stock, such that:
--
--   1. $s_k\le S_k$ for every $k<T$, and $s_k=S_k$ for every $k<T$ if $K=0$;
--   2. for every period $k<T$ and every stock $x$ at its beginning, the rule
--   $$u_i=\begin{cases}S_i-x'_i&\text{if }x'_i<s_i,\\0&\text{otherwise,}\end{cases}\qquad x'_{i+1}=x'_i+u_i-w'_i,\quad x'_k=x,$$
--   minimizes $\sum_{i=k}^{T-1}[C(u_i)+R(x'_{i+1})]$ over all nonnegative orders for periods $k,\dots,T-1$, where $C(u)=K\mathbf 1_{\{u>0\}}+cu$ and $R(x)=\max(hx,-px)$;
--   3. for every initial stock $x_0$, the orders that this rule generates from $x_0$ are the order part of an optimal solution of the robust formulation (14) with that initial stock.
--
--   The robust policy therefore keeps the base-stock structure of the nominal and stochastic policies.
--
--   **Formalization Note** The rule acts on the modified stock $x'$. Quantifying the thresholds before the stock is essential: thresholds fitted to a single trajectory would exist for any optimal order sequence. The statement gives no formula for the thresholds; Theorem 3.2(b), (c) do.
--
--   Differences from the source:
--   - reading: "it is (S, S) if there is no fixed cost and (s, S) if there is a fixed cost" → thresholds independent of the stock whose rule is optimal for the modified nominal problem from every period and modified stock, and generates a robust optimum from every initial stock; reason: Definition 3.1 applies the thresholds to the current stock, and the proof identifies that stock as the modified stock x′
--   - reading: A_k = q*_kΓ_k + Σ r*_ik for the optimal q*, r* of (14) → A_k is the optimal value of LP (13); reason: the optimal q*, r* need not be unique (h = 0), and Remark 1 after Theorem 3.2 defines A_k by (13); the published base items use the same reading
--   - encoding: binary variables v_k with 0 ≤ u_k ≤ M v_k, M a large number → the fixed-cost indicator K·1{u_k > 0} of (21); reason: the two agree for M large enough; this is the convention of the published definitions
--   - generalization: the demand is always nonnegative, ŵ_k ≤ w̄_k (p. 156) → no sign condition on w̄ or w′; reason: the statement holds without it, and nonnegative demand is a special case
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 155 (PDF 6), Theorem 3.2(a), last sentence; p. 154 (PDF 5), Definition 3.1

import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust
import Definitions.Def_RobustInventory_SingleStation_Supplement_Policy

namespace RobustInventory.SingleStation.Supplement

/-- Theorem 3.2(a), last sentence, p. 155: the optimal robust policy is `(s, S)` on the modified
stock, and `(S, S)` without fixed cost. There are thresholds `s_k ≤ S_k`, chosen before any
stock, with `s_k = S_k` if `K = 0`, whose rule is optimal for the modified nominal problem that
remains from every period and every stock, and whose orders from every initial stock `x₀` are
the order part of an optimal solution of (14) with that initial stock. -/
theorem theorem_3_2a_structure (M : Model) :
    ∃ s S : ℕ → ℝ,
      (∀ k < M.T, s k ≤ S k) ∧
      (M.K = 0 → ∀ k < M.T, s k = S k) ∧
      (∀ k < M.T, ∀ x : ℝ, IsTailOptimal M M.wmod k x (sSPolicy s S M.wmod k x)) ∧
      ∀ x₀ : ℝ, ∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ),
        ({ M with x0 := x₀ } : Model).IsRobustOptimal (sSPolicy s S M.wmod 0 x₀) y q r := by sorry

end RobustInventory.SingleStation.Supplement

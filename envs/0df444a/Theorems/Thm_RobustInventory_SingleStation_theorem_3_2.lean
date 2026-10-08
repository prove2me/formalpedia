-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_theorem_3_2
-- name    : RobustInventory.SingleStation.theorem_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:32:38.677729+00:00
-- url     : https://prove2.me/theorems/6f2d8d29-0bff-4e22-93b0-51670faf5b83
-- title:
--   Theorem 3.2 (a), (b), (d), p. 155 — the optimal robust policy is the optimal nominal policy for the modified demand $w'$
-- statement:
--   **Theorem 3.2 (Optimal Robust Policy).** Consider the single-station model of §3.1. Let $A_k$ be the optimal value of LP (13) (with $A_{-1} = 0$), let
--   $$w'_k = \bar w_k + \frac{p-h}{p+h}\,(A_k - A_{k-1})$$
--   be the modified demand (20), and let $\kappa = \frac{2ph}{p+h}$. Write $N_{w'}(u) = \sum_{k=0}^{T-1}\big(C(u_k) + \max(hx'_{k+1}, -px'_{k+1})\big)$ for the cost of the nominal problem with demand $w'$, where $x'_{k+1} = x_0 + \sum_{i=0}^{k}(u_i - w'_i)$.
--
--   1. **(d), for every order sequence.** For every $u$ with $u_k \ge 0$ ($k < T$), every $(y, q, r)$ feasible in the robust formulation (14) together with $u$ has objective at least
--   $$N_{w'}(u) + \kappa\sum_{k=0}^{T-1} A_k,$$
--   and some feasible $(y, q, r)$ attains this value.
--   2. **(a).** An order sequence $u$ is the order part of an optimal solution of (14) if and only if $u$ is optimal for the nominal problem with demand $w'$.
--   3. **(d), optimal costs.** If $(u, y, q, r)$ is optimal for (14) and $u'$ is optimal for the nominal problem with demand $w'$, then the optimal cost of (14) is
--   $$\sum_{k=0}^{T-1}\big(C(u_k) + y_k\big) = N_{w'}(u') + \frac{2ph}{p+h}\sum_{k=0}^{T-1} A_k.$$
--   4. **(b).** If there is no fixed cost ($K = 0$) and $w'_k \ge 0$ for $k < T$, the order-up-to policy with $S_k = w'_k$, run along the modified trajectory ($x'_0 = x_0$, $u_k = \max(w'_k - x'_k, 0)$, $x'_{k+1} = x'_k + u_k - w'_k$), is the order part of an optimal solution of (14).
--
--   The robust problem thus keeps the structure of the nominal one: it is a nominal problem with a deterministic modified demand that shifts the base-stock levels by $\frac{p-h}{p+h}(A_k - A_{k-1})$, and robustness costs exactly $\frac{2ph}{p+h}\sum_k A_k$ more.
--
--   **Formalization Note** The policy is the order sequence chosen at time 0 for the whole horizon ("evaluated at time 0 for the rest of the horizon"). $A_k$ is the value of (13) rather than "$q^*_k\Gamma_k + \sum_i r^*_{ik}$ for the optimal $q^*, r^*$ of (14)", which is not unique in general (e.g. $h = 0$); Remark 1 after the theorem uses (13) the same way. The robust formulation is (14) with the $k$-th constraint pair protected by the budget $\Gamma_k$ alone, as printed; the fixed cost is the indicator of (21) instead of binary variables with a big-$M$. Part (b) is stated under $w'_k \ge 0$, which holds whenever $p \ge h$ and $\bar w_k \ge 0$ (Remark 1). As printed, (b) is false when $p < h$ makes $w'_k$ negative: for $T = 2$, $x_0 = 0$, $\bar w = (10, 0)$, $\hat w = (10, 0)$, $\Gamma = (0, 1)$, $c = 1$, $h = 4$, $p = 2$ one has $A = (0, 10)$, $w' = (10, -10/3)$; the policy $S_k = w'_k$ orders $(10, 0)$ at robust cost $50$, while the orders $(20/3, 0)$ cost $40$. The (s, S) clause of (a) and part (c) are not part of this statement: they rest on Lemma 3.1(a), the stochastic (s, S) theorem cited from Bertsekas (1995), and on the thresholds (15)–(16) of Lemma 3.1(c).
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 155 (PDF 6), §3.1, Theorem 3.2 (a), (b), (d) and its proof; p. 156 (PDF 7), Remark 1

import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust

namespace RobustInventory.SingleStation

open Finset

/-- Theorem 3.2 (Optimal Robust Policy), (a), (b) and (d), p. 155. Let `A_k` be the optimal value
of (13), `w'` the modified demand (20) and `κ = 2ph/(p + h)`.
1. (d), for every order sequence: for every nonnegative `u`, every `(y, q, r)` feasible in (14)
   has objective at least `nominalCost w' u + κ ∑_{k<T} A_k`, and some feasible `(y, q, r)`
   attains it.
2. (a): `u` is the order part of an optimal solution of (14) iff `u` is optimal for the nominal
   problem with demand `w'`.
3. (d), optimal values: the optimal cost of (14) equals the optimal nominal cost under `w'`
   plus `κ ∑_{k<T} A_k`.
4. (b): without fixed cost, and when `w'_k ≥ 0` for `k < T`, the order-up-to policy with
   `S_k = w'_k` (along the modified trajectory) is the order part of an optimal solution of (14). -/
theorem theorem_3_2 (M : Model) :
    (∀ u : ℕ → ℝ, (∀ k < M.T, 0 ≤ u k) →
      (∀ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), M.RobustFeasible u y q r →
        M.nominalCost M.wmod u + 2 * M.p * M.h / (M.p + M.h) * ∑ k ∈ range M.T, M.A k
          ≤ M.robustObjective u y) ∧
      (∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), M.RobustFeasible u y q r ∧
        M.robustObjective u y =
          M.nominalCost M.wmod u + 2 * M.p * M.h / (M.p + M.h) * ∑ k ∈ range M.T, M.A k)) ∧
    (∀ u : ℕ → ℝ,
      (∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), M.IsRobustOptimal u y q r) ↔
        M.IsNominalOptimal M.wmod u) ∧
    (∀ (u y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (u' : ℕ → ℝ),
      M.IsRobustOptimal u y q r → M.IsNominalOptimal M.wmod u' →
        M.robustObjective u y =
          M.nominalCost M.wmod u' + 2 * M.p * M.h / (M.p + M.h) * ∑ k ∈ range M.T, M.A k) ∧
    (M.K = 0 → (∀ k < M.T, 0 ≤ M.wmod k) →
      ∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ),
        M.IsRobustOptimal (orderUpTo M.x0 M.wmod M.wmod) y q r) := by sorry

end RobustInventory.SingleStation

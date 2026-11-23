-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_Supplement_theorem_3_2c
-- name    : RobustInventory.SingleStation.Supplement.theorem_3_2c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:28:30.537282+00:00
-- url     : https://prove2.me/theorems/58fa538d-48f4-4583-a4c2-c7e9c7f36eba
-- title:
--   Theorem 3.2(c), p. 155: thresholds (15)–(16) at the modified demand give the robust policy with fixed cost (corrected: $w'_k\ge0$ required)
-- statement:
--   **Theorem 3.2(c), corrected.** Consider the single-station model of §3.1 with fixed cost $K>0$ and unit costs $c>0$, $h\ge0$, $p>c$. Let $A_k$ be the value of LP (13), $A_{-1}=0$, and $w'_k=\bar w_k+\frac{p-h}{p+h}(A_k-A_{k-1})$ the modified demand (20), and suppose $w'_k\ge0$ for $k<T$.
--
--   Let $t_1<\dots<t_J$ be the ordering times of any optimal solution of the robust formulation (14), $t_{J+1}=T$, $L_j=t_{j+1}-t_j$ and $I_j=\lfloor(pL_j-c\mathbf 1_{\{j=J\}})/(h+p)\rfloor$. Evaluate (15) and (16) at $w'$:
--   $$S_j=\sum_{i=0}^{I_j}w'_{t_j+i},\qquad s_1=x_0-\sum_{i=0}^{t_1-1}w'_i,\qquad s_j=-\sum_{i=I_{j-1}+1}^{L_{j-1}-1}w'_{t_{j-1}+i}\quad(j\ge2).$$
--   Then some optimal solution of (14) orders exactly at $t_1,\dots,t_J$, and at each $t_j$ its modified stock $x'$, with $x'_0=x_0$ and $x'_{k+1}=x'_k+v_k-w'_k$ for its orders $v$, satisfies
--   $$x'_{t_j}=s_j,\qquad x'_{t_j}+v_{t_j}=S_j .$$
--
--   With fixed costs and given ordering times, the robust policy is thus available in closed form.
--
--   **Formalization Note** As printed, without $w'\ge0$, the statement is false. For $T=2$, $x_0=0$, $\bar w=\hat w=(10,0)$, $\Gamma=(0,1)$, $c=1$, $h=4$, $p=2$, $K=0.1$ every assumption of the paper holds, nonnegative demand included, and $w'=(10,-10/3)$. The only optimal ordering time is $0$ and the optimal order is $20/3$, with robust cost $40.1$, while (15) gives $S_1=10$, with robust cost $50.1$. The added condition is automatic when $p\ge h$ and $\bar w\ge0$, because $A_k$ is nondecreasing; it excludes only data for which some $w'_k$ is negative.
--
--   Differences from the source:
--   - correction: (15)–(16) at w′ give the thresholds whenever there is a fixed cost → the same conclusion under w′_k ≥ 0 for k < T; reason: false as printed: T = 2, x_0 = 0, w̄ = ŵ = (10, 0), Γ = (0, 1), c = 1, h = 4, p = 2, K = 0.1 gives w′ = (10, −10/3) and S_1 = 10 at cost 50.1, while the optimum orders 20/3 at cost 40.1; the proof invokes Lemma 3.1(c), which needs a nonnegative demand. Excluded: data with some w′_k < 0, which under nonnegative demand needs p < h
--   - reading: "the corresponding thresholds S_j, s_j" at the ordering times → some robust optimum with exactly those ordering times has modified stock s_j before and S_j after each order; reason: minimizers are not unique, and the proof of Theorem 3.2 works in the modified stock x′
--   - reading: s_j is the reorder threshold, and Definition 3.1 orders when x < s → the modified stock before the order at t_j equals s_j; reason: Lemma 3.1(c) defines s_j as that stock, so equality triggers the order
--   - reading: A_k = q*_kΓ_k + Σ r*_ik for the optimal q*, r* of (14) → A_k is the optimal value of LP (13); reason: the optimal q*, r* need not be unique (h = 0), and Remark 1 after Theorem 3.2 defines A_k by (13); the published base items use the same reading
--   - encoding: binary variables v_k with 0 ≤ u_k ≤ M v_k, M a large number → the fixed-cost indicator K·1{u_k > 0} of (21); reason: the two agree for M large enough; this is the convention of the published definitions
--   - generalization: the demand is always nonnegative, ŵ_k ≤ w̄_k (p. 156) → only w′_k ≥ 0 is assumed; reason: only the modified demand enters the thresholds; for p ≥ h nonnegative demand implies w′ ≥ 0
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 155 (PDF 6), Theorem 3.2(c); p. 154 (PDF 5), Lemma 3.1(c), Eqs. (15)–(16)

import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust
import Definitions.Def_RobustInventory_SingleStation_Supplement_Thresholds

namespace RobustInventory.SingleStation.Supplement

/-- Theorem 3.2(c), p. 155, for `K > 0` and `w'_k ≥ 0` on the horizon: if `t_1 < … < t_J` are
the ordering times of an optimal solution of (14), then some optimal solution of (14) orders
exactly at these times, and at each `t_j` its modified stock is `s_j` before the order and `S_j`
after it, (15)–(16) being evaluated at the modified demand `w'`. -/
theorem theorem_3_2c (M : Model) (hK : 0 < M.K) (hw' : ∀ k < M.T, 0 ≤ M.wmod k)
    (u y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (hu : M.IsRobustOptimal u y q r)
    (J : ℕ) (t : ℕ → ℕ) (ht : IsOrderingTimes M.T u J t) :
    ∃ (v y' q' : ℕ → ℝ) (r' : ℕ → ℕ → ℝ),
      M.IsRobustOptimal v y' q' r' ∧ IsOrderingTimes M.T v J t ∧
      ∀ j ∈ Finset.Icc 1 J,
        stockBefore M M.wmod v (t j) = lowerThreshold M M.wmod J t j ∧
        stockBefore M M.wmod v (t j) + v (t j) = upperThreshold M M.wmod J t j := by sorry

end RobustInventory.SingleStation.Supplement

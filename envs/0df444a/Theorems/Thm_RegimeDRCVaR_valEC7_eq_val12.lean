-- Prove2me | Theorems.Thm_RegimeDRCVaR_valEC7_eq_val12
-- name    : RegimeDRCVaR.valEC7_eq_val12
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:25:52.063006+00:00
-- url     : https://prove2.me/theorems/c39b1e06-d010-4e0b-b88b-e845824e7fd3
-- title:
--   Proof of Theorem 1 — merging the regime multipliers: (EC.7) and (12) have the same value
-- statement:
--   In the setting of Theorem 1, the optimal value of (EC.7), which has one multiplier $\beta_k\ge\|x\|_{m^*}$ per regime, equals the optimal value of (12), which has a single $\beta\ge\|x\|_{m^*}$:
--   $$
--   \min_{(EC.7)}\ v+\frac1{1-\eta}\Big[\sum_{k,n}\frac{w_k}{N_k}\alpha_{nk}+\sum_k\beta_kw_k\theta_k\Big]
--   =\min_{(12)}\ v+\frac1{1-\eta}\Big[\sum_{k,n}\frac{w_k}{N_k}\alpha_{nk}+\beta\sum_kw_k\theta_k\Big].
--   $$
--
--   This is the last step from (11) to the reformulation (12).
--
--   **Formalization Note** The paper justifies the merge "since $w_k\theta_k>0$"; the identity is stated for all $w_k\theta_k\ge0$, the setting of Theorem 1.
--
--   Differences from the source:
--   - encoding: standing assumptions of §3 (m ∈ [1,+∞], η ∈ (0,1), N_k sample counts, w_k regime probabilities, θ_k radii) → hypotheses 1 ≤ m, 0 < η < 1, 0 < N k, 0 ≤ w k, ∑ w = 1, 0 ≤ θ k; reason: the paper's setting, made explicit; no other hypothesis is added
--   - encoding: ℓm norm ‖·‖_m and conjugate norm ‖·‖_{m*} on ℝ^I → normM m (the PiLp m norm on Fin I → ℝ) and normM (ENNReal.conjExponent m); reason: Lean convention; ENNReal.conjExponent sends 1 ↦ ∞, 2 ↦ 2, ∞ ↦ 1, the Hölder conjugate
--   - encoding: sup and min of real-valued problems → worst case as an ℝ≥0∞ supremum of lower integrals; objectives of (11) and optimal values as EReal infima; reason: Lean convention; the loss is nonnegative and the values are finite on every instance where the source's are, ±∞ otherwise
--   - encoding: regimes k ∈ [K], scenarios n ∈ [N_k], samples r_nk → k : Fin K, n : Fin (N k), r k n; reason: Lean convention; index i − 1 for paper index i
--   - generalization: the merge argument 'since w_kθ_k > 0, ∀k ∈ [K]' → no positivity hypothesis: w_kθ_k ≥ 0 from 0 ≤ w k, 0 ≤ θ k; reason: Theorem 1 assumes no positivity (Remark 1 takes θ = 0); the identity holds for w_kθ_k ≥ 0 and specializes to the case w_kθ_k > 0
--   - generalization: 𝒳 = {x | Ax = b, Cx ≥ d} with the budget constraint 1′x = 1 embedded in it as a necessary constraint (p.9) → feasX A b C d for arbitrary A, b, C, d (no budget row required); reason: the argument never uses the budget row; the source’s 𝒳 is the instance in which one row of (A, b) is (1′, 1)
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, proof of Theorem 1, p.ec3 after (EC.7)

import Mathlib
import Definitions.Def_RegimeDRCVaR_valEC7
import Definitions.Def_RegimeDRCVaR_val12

open scoped ENNReal

namespace RegimeDRCVaR

/-- **Proof of Theorem 1, merging the regime multipliers** (Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, p.ec3): "Note that in (EC.7), if there exists β*_i ≠ β*_j for some
i, j ∈ [K] in the optimal solution, then we can always reduce both β_i, β_j := min(β*_i, β*_j) and
keeping other variables the same to obtain a new feasible solution while reducing its objective
value since w_kθ_k > 0, ∀k ∈ [K]. Therefore, we have an implicit constraint β_k = β, ∀k ∈ [K].
Combining it with the current constraint, we obtain the reformulation, i.e. (12)."

The optimal value of (EC.7) (one multiplier `β_k` per regime) equals the optimal value of (12)
(one multiplier `β`).

**Formalization Note** "since w_kθ_k > 0" is a step of the paper's argument, not a hypothesis of
Theorem 1; the value identity holds for all `w_kθ_k ≥ 0`, which is what is stated. Standing
assumptions of §3: `m ∈ [1, ∞]`, `η ∈ (0, 1)`, `N_k ≥ 1`, `w` a probability vector, `θ_k ≥ 0`.
Optimal values are `EReal` infima. -/
theorem valEC7_eq_val12 {I K p q : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞) (hm : 1 ≤ m)
    (r : (k : Fin K) → Fin (N k) → Fin I → ℝ) (w θ : Fin K → ℝ) (η : ℝ)
    (hN : ∀ k, 0 < N k) (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (hθ : ∀ k, 0 ≤ θ k)
    (hη0 : 0 < η) (hη1 : η < 1)
    (A : Matrix (Fin p) (Fin I) ℝ) (b : Fin p → ℝ) (C : Matrix (Fin q) (Fin I) ℝ)
    (d : Fin q → ℝ) :
    valEC7 m r w θ η A b C d = val12 m r w θ η A b C d := by sorry

end RegimeDRCVaR

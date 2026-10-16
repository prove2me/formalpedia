-- Prove2me | Theorems.Thm_PooledRationing_AsymFeas_theorem_1
-- name    : PooledRationing.AsymFeas.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:37.418385+00:00
-- url     : https://prove2.me/theorems/83d5563b-6b64-4e3b-886d-75e8cf3284fc
-- title:
--   Theorem 1 — characterization of asymptotically feasible capacity
-- statement:
--   In the pooled-resource model, a fixed nonnegative capacity vector $c$ is asymptotically feasible if and only if its expected maximum weighted service meets every nonnegative weighted sum of the customer targets:
--   $$
--   c\text{ is asymptotically feasible}\quad\Longleftrightarrow\quad
--   \mathbb E_F\!\left[\max_{(s,y)\in P(c,D)}\sum_jw_jR_j(s_j,D_j)\right]
--   \ge\sum_jw_j\beta_j\quad\text{for every }w\ge0.
--   $$
--   Asymptotic feasibility means that for each $\varepsilon>0$ a randomized rationing policy achieves expected service at least $\beta_j-\varepsilon$ for every customer $j$. The equivalence turns a simultaneous service requirement into a family of weighted optimization tests.
--
--   **Formalization Note** Customers and resources use zero-based finite indices. The demand law has a bounded second moment and nonnegative demand, targets lie in $(0,1)$, and Assumption 1's monotonicity, upper semicontinuity, and compactness are explicit. The service measure is extended from the paper's nonnegative domain to all real inputs, is nonnegative and jointly measurable, and is bounded on feasible decisions by an integrable envelope. For each nonnegative weight vector a measurable maximizing feasible selection is assumed, making the expectation of the maximum meaningful. Randomized policies are finite mixtures of measurable deterministic policies; they represent the finite expected-service vectors of the paper's probability measures over policies. The weighted test ranges over all nonnegative vectors, while the simplex appears only in the minimax milestone.
-- source:
--   Jiang, Wang & Zhang, Achieving High Individual Service-Levels without Safety Stock? Optimal Rationing Policy of Pooled Resources, SSRN 3385089 (version of 31 July 2021), p. 13, Theorem 1, (18)

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting

namespace PooledRationing.AsymFeas

open MeasureTheory

/-- Jiang–Wang–Zhang, Theorem 1, equation (18), p. 13. -/
theorem theorem_1 {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)) (c : Fin m → ℝ)
    (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (hc : 0 ≤ c) (hβ : ∀ j, β j ∈ Set.Ioo 0 1)
    (hF2 : MemLp id 2 F) (hDnn : ∀ᵐ D ∂F, (0 : Fin n → ℝ) ≤ D)
    (hA1_mono : ∀ j d, Monotone (fun s => R j s d))
    (hA1_usc : ∀ j d, UpperSemicontinuous (fun s => R j s d))
    (hA1_compact : ∀ D, IsCompact (P c D))
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (h : (Fin n → ℝ) → ℝ) (hh : Integrable h F)
    (hRenv : ∀ D, ∀ x ∈ P c D, ∀ j, R j (x.1 j) (D j) ≤ h D)
    (hsel : ∀ w : Fin n → ℝ, 0 ≤ w → ∃ φ : DetPolicy P c,
      ∀ D, IsMaxOn (weightedService R w D) (P c D) (φ.toFun D)) :
    IsAsymFeasible F R β P c ↔
      ∀ w : Fin n → ℝ, 0 ≤ w →
        ∑ j, w j * β j ≤ ∫ D, maxWeightedValue P c R w D ∂F := by sorry

end PooledRationing.AsymFeas

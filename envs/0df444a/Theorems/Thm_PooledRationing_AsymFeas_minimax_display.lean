-- Prove2me | Theorems.Thm_PooledRationing_AsymFeas_minimax_display
-- name    : PooledRationing.AsymFeas.minimax_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:35.363617+00:00
-- url     : https://prove2.me/theorems/2485c118-78c2-4801-bd70-7bbd16f894bc
-- title:
--   Display after (20), equation (21) — an approximate minimax policy
-- statement:
--   Suppose the weighted-service condition (18) holds for every nonnegative vector $w$. For every $\varepsilon>0$ there is a randomized policy $\lambda_\varepsilon$ such that
--   $$
--   \sum_j w_j\bigl(\beta_j-S_j(\lambda_\varepsilon)\bigr)\le\varepsilon
--   \qquad\text{for every }w\ge0\text{ with }\sum_jw_j\le1.
--   $$
--   Here $S_j(\lambda)$ is the expected service of customer $j$. This is the approximate policy supplied by the minimax step in the proof of Theorem 1.
--
--   **Formalization Note** The policy measure is represented by a finite mixture, which has the same finite service vector for the statements here. The demand law has a bounded second moment and nonnegative demand, capacities are nonnegative, and the service targets lie in $(0,1)$. Assumption 1 is explicit. The nonnegative service measure is extended to all real inputs and is jointly measurable. An integrable envelope bounds service, and a measurable maximizing selection is assumed for every nonnegative weight vector so that the expected maximum in (18) is well defined. These are the regularity pins implicit in the paper's expectations and tie-breaking.
-- source:
--   Jiang, Wang & Zhang, Achieving High Individual Service-Levels without Safety Stock? Optimal Rationing Policy of Pooled Resources, SSRN 3385089 (version of 31 July 2021), p. 13, proof of Theorem 1, display after (20) and (21)

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting

namespace PooledRationing.AsymFeas

open MeasureTheory

/-- The display following equation (20), expressed in the approximate form (21), p. 13. -/
theorem minimax_display {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
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
      ∀ D, IsMaxOn (weightedService R w D) (P c D) (φ.toFun D))
    (h18 : ∀ w : Fin n → ℝ, 0 ≤ w →
      ∑ j, w j * β j ≤ ∫ D, maxWeightedValue P c R w D ∂F) :
    ∀ ε : ℝ, 0 < ε → ∃ lam : RandPolicy P c,
      ∀ w : Fin n → ℝ, 0 ≤ w → (∑ j, w j) ≤ 1 →
        ∑ j, w j * (β j - service F R lam j) ≤ ε := by sorry

end PooledRationing.AsymFeas

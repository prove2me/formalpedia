-- Prove2me | Theorems.Thm_WeightedMajority_General_appendix_mistake_step
-- name    : WeightedMajority.General.appendix_mistake_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:45.767979+00:00
-- url     : https://prove2.me/theorems/884a70ef-7a8b-4ac4-b524-c4c2892a7f34
-- title:
--   Appendix, p. 256 — a mistake of WMG multiplies the total weight by at most (1+β)/2
-- statement:
--   Let $0 \le \beta < 1$ and consider a run of the algorithm WMG with parameter $\beta$ on a pool of $n$ algorithms with predictions $x_{k,i} \in [0,1]$ and binary labels $\rho_k$, with weights $w_{k,i}$ and total weights $s_k = \sum_i w_{k,i}$. If WMG makes a mistake in trial $k$, that is, its prediction $\lambda_k$ differs from $\rho_k$, then the total weight after the update is at most a fraction $(1+\beta)/2$ of the total weight before it:
--
--   $$
--   s_{k+1} \le \frac{1+\beta}{2}\, s_k .
--   $$
--
--   In the notation of the Appendix, with $q_0 = \sum_i w_{k,i}(1 - x_{k,i})$ and $q_1 = \sum_i w_{k,i} x_{k,i}$, the total weight before the trial is $q_0 + q_1$ and the claim is that it is at most $\frac{1+\beta}{2}(q_0+q_1)$ afterwards.
--
--   This is the step on which the alternate proof of Theorem 5.1 in the Appendix rests.
--
--   **Formalization Note** The run is the relation `IsWMGRun`; the claim holds for every choice of tie-breaking, update flags and factors allowed by (5.1).
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 256, Appendix, alternate proof of Theorem 5.1

import Mathlib
import Definitions.Def_WeightedMajority_General_WMGRun

namespace WeightedMajority.General

/-- Appendix, p. 256 (alternate proof of Theorem 5.1): in a trial in which WMG makes a mistake,
the total weight after the update is at most `(1 + β) / 2` times the total weight before it. -/
theorem appendix_mistake_step {n T : ℕ} {β : ℝ} {x : Fin T → Fin n → ℝ} {ρ : Fin T → ℝ}
    {w : ℕ → Fin n → ℝ} {pred : Fin T → ℝ} {upd : Fin T → Bool} {F : Fin T → Fin n → ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hrun : IsWMGRun β x ρ w pred upd F)
    (k : Fin T) (hmis : pred k ≠ ρ k) :
    WeightedMajority.Basic.totalWeight w (k.val + 1) ≤ (1 + β) / 2 * WeightedMajority.Basic.totalWeight w k.val := by sorry

end WeightedMajority.General

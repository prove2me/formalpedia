-- Prove2me | Theorems.Thm_ServTimeLimit_OptMech_full_extraction
-- name    : ServTimeLimit.OptMech.full_extraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:46.625466+00:00
-- url     : https://prove2.me/theorems/df5b01dd-b72b-4e1f-be95-6abd7ea0c2ae
-- title:
--   Proof of Theorem 8, p. 47 — the price p(θ) = min{θ, t(θ)} − cW is IC, leaves zero utility to every type, and earns revenue equal to welfare
-- statement:
--   Assume $\Lambda, c, \bar\theta > 0$, let $(\Phi, t)$ be a feasible allocation with waiting time $W = W(\Phi, t)$, and set
--   $$p(\theta) = \min\{\theta, t(\theta)\} - cW .$$
--   Then:
--   1. $(\Phi, t, p)$ is incentive compatible: $\min\{t(\theta'),\theta\} - p(\theta') \le \min\{t(\theta),\theta\} - p(\theta)$ for all $\theta, \theta' \in \Phi$;
--   2. every admitted type reporting truthfully gets zero utility: $\min\{t(\theta),\theta\} - p(\theta) - cW = 0$ for $\theta \in \Phi$;
--   3. a type $\theta \in [0,\bar\theta] \setminus \Phi$ that is not admitted gains nothing by claiming an admitted type $\theta' \in \Phi$: $\min\{t(\theta'),\theta\} - p(\theta') - cW \le 0$;
--   4. the revenue equals the social welfare: $\pi(\Phi, p) = SW(\Phi, t)$.
--
--   This is the lower half of Theorem 8: the firm can extract all consumer surplus of any feasible allocation.
--
--   **Formalization Note** The proof writes $p(\theta) = t(\theta) - cW$; Theorem 8 writes $\min\{\theta, t(\theta)\} - cW$. These agree on $\Phi$, where $t(\theta) \le \theta$; the theorem's form is used. Non-negativity of this price is not part of this statement (it can fail for an arbitrary allocation); for the first-best allocations it is a clause of the goal.
-- source:
--   Feldman & Segev, The Important Role of Time Limits when Consumers Choose their Time in Service, SSRN 3424317 (version of 2021-10-07), p. 47, proof of Theorem 8

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model

namespace ServTimeLimit.OptMech

open MeasureTheory

/-- Proof of Theorem 8, p. 47: for any feasible allocation `(Φ, t)`, the price
`p(θ) = min{θ, t(θ)} − c W` is incentive compatible, leaves every admitted truthful consumer zero
utility, gives a non-admitted type no gain from claiming an admitted type, and makes revenue equal
social welfare. -/
theorem full_extraction (P : Params) (hP : P.Standing) (Φ : Set ℝ) (t : ℝ → ℝ)
    (hA : IsAllocation P Φ t) (p : ℝ → ℝ)
    (hp : ∀ θ, p θ = min θ (t θ) - P.c * waitTime P Φ t) :
    IsIC Φ t p ∧
    (∀ θ ∈ Φ, min (t θ) θ - p θ - P.c * waitTime P Φ t = 0) ∧
    (∀ θ ∈ Set.Icc 0 P.θbar \ Φ, ∀ θ' ∈ Φ, min (t θ') θ - p θ' - P.c * waitTime P Φ t ≤ 0) ∧
    revenue P Φ p = welfare P Φ t := by sorry

end ServTimeLimit.OptMech

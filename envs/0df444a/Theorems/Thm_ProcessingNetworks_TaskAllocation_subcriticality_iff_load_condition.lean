-- Prove2me | Theorems.Thm_ProcessingNetworks_TaskAllocation_subcriticality_iff_load_condition
-- name    : ProcessingNetworks.TaskAllocation.subcriticality_iff_load_condition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T19:41:34.607896+00:00
-- url     : https://prove2.me/theorems/0d6dd594-88c0-468e-9829-5cfac8b0a7de
-- title:
--   Lemma 11.2 — subcriticality via a simplified LP-type criterion (milestone)
-- statement:
--   **Lemma 11.2.** The task allocation model is subcritical iff there exists $\lambda =
--   (\lambda_{\ell k}) \ge 0$ with $\sum_{k} \lambda_{\ell k} = \nu_\ell$ for each category $\ell$
--   (11.4), and $\sum_{\ell} m_{\ell k}\lambda_{\ell k} < 1$ for each server $k$ (11.5).
--
--   This restates general SPN subcriticality (Eq. 11.6) in this model's own, much simpler
--   LP-feasibility terms, eliminating the auxiliary variable $x = M\lambda$ and the general
--   $G,R,A,b$ machinery entirely.
--
--   **Formalization note.** `IsSubcriticalGeneral` is this model's own instantiation of Eq. 11.6
--   (`TaskAllocationModel`'s own item); this lemma is the genuine content of eliminating the
--   auxiliary variable `x` to reach the simplified criterion.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 215, Lemma 11.2, Eqs. (11.4)-(11.6)

import Mathlib
import Definitions.Def_ProcessingNetworks_TaskAllocation_TaskAllocationModel

namespace ProcessingNetworks.TaskAllocation

/-- Lemma 11.2, Dai & Harrison p. 215 (PDF p. 231): the task allocation model is subcritical
(`IsSubcriticalGeneral`, Eq. 11.6 specialized to this model) if and only if there exists an
`I`-vector `λ = (λℓk) ≥ 0` such that `∑_k λℓk = νℓ` for each category `ℓ` (11.4), and
`∑_ℓ mℓk λℓk < 1` for each server `k` (11.5). -/
theorem subcriticality_iff_load_condition
    {L K : ℕ} (dat : TaskAllocationData L K) :
    IsSubcriticalGeneral dat ↔
      ∃ lam : Fin L → Fin K → ℝ, (∀ ℓ k, 0 ≤ lam ℓ k) ∧
        (∀ ℓ, ∑ k, lam ℓ k = dat.nu ℓ) ∧ (∀ k, ∑ ℓ, dat.m ℓ k * lam ℓ k < 1) := by sorry

end ProcessingNetworks.TaskAllocation

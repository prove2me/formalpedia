-- Prove2me | Theorems.Thm_ProcessingNetworks_TaskAllocation_wwta_fluid_stable_of_load_condition
-- name    : ProcessingNetworks.TaskAllocation.wwta_fluid_stable_of_load_condition
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:43:47.109577+00:00
-- url     : https://prove2.me/theorems/c77a34a2-2986-4539-82d0-7452bbd1e44a
-- title:
--   Theorem 11.6 — WWTA fluid model stability under the load condition (goal)
-- statement:
--   This is the goal theorem of the mission.
--
--   **Theorem 11.6.** Suppose there exists $\lambda = (\lambda_{\ell k}) \ge 0$ satisfying (11.4)
--   and (11.5). Then the WWTA fluid model is stable.
--
--   The book's own proof exhibits an explicit quadratic Lyapunov function $f(t) := \tfrac12
--   \sum_k W_k(t)^2$ and shows $\dot f(t) \le -\varepsilon\sum_k W_k(t) \le -\varepsilon\sqrt{2f(t)}$
--   for $\varepsilon := \min_k(1 - \sum_\ell \lambda_{\ell k}m_{\ell k}) > 0$, so $f$ (hence $W$,
--   hence $Z$) reaches $0$ in finite time by Lemma 8.6.
--
--   **Formalization note.** The hypothesis is exactly (11.4)-(11.5) (`hload`); the conclusion
--   `WWTAFluidStable` is Definition 6.3 (mission III) specialized to the WWTA fluid model. The
--   book's own further corollary "thus the task allocation model itself is stable under WWTA"
--   (via Theorem 11.5) is not restated in this goal's own conclusion, matching how mission IX's own
--   goal theorem states only the fluid-stability conclusion proper.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 220, Theorem 11.6

import Mathlib
import Definitions.Def_ProcessingNetworks_TaskAllocation_TaskAllocationModel
import Definitions.Def_ProcessingNetworks_TaskAllocation_FluidModel

namespace ProcessingNetworks.TaskAllocation

/-- Theorem 11.6, Dai & Harrison p. 220 (PDF p. 236) — the goal theorem of this mission: suppose
there exists an `I`-vector `λ = (λℓk) ≥ 0` satisfying (11.4) and (11.5). Then the WWTA fluid model,
defined by equations (11.11)-(11.16), is stable. (The book's own further sentence, "thus, by
Theorem 11.5 above, the task allocation model itself is stable under the WWTA routing policy," is
Theorem 11.5 applied to this conclusion, not new content of Theorem 11.6 itself, and is not
restated here — matching how mission IX's goal theorem states only the fluid-stability conclusion
proper.) -/
theorem wwta_fluid_stable_of_load_condition
    {L K : ℕ} [Nonempty (Fin K)] (dat : TaskAllocationData L K)
    (hload : ∃ lam : Fin L → Fin K → ℝ, (∀ ℓ k, 0 ≤ lam ℓ k) ∧
      (∀ ℓ, ∑ k, lam ℓ k = dat.nu ℓ) ∧ (∀ k, ∑ ℓ, dat.m ℓ k * lam ℓ k < 1)) :
    WWTAFluidStable dat := by sorry

end ProcessingNetworks.TaskAllocation

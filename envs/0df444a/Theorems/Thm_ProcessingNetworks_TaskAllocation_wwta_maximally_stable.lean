-- Prove2me | Theorems.Thm_ProcessingNetworks_TaskAllocation_wwta_maximally_stable
-- name    : ProcessingNetworks.TaskAllocation.wwta_maximally_stable
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:44:16.56152+00:00
-- url     : https://prove2.me/theorems/aa9fc55c-54c2-4c40-85a3-87dff3d7565e
-- title:
--   Corollary 11.7 — WWTA is maximally stable (milestone)
-- statement:
--   **Corollary 11.7.** The WWTA routing policy is maximally stable: if there exists any simply
--   structured routing policy under which the task allocation model is stable, then it is stable
--   under WWTA.
--
--   The book's own proof is immediate from Corollary 5.5 (stability under any policy implies
--   subcriticality) together with Lemma 11.2 and Theorem 11.6.
--
--   **Formalization note.** A control policy is an abstract value of a type `Policy`, with
--   `PolicyStable p` recording model stability under `p` (positive recurrence of the ambient
--   chain). `hnecessary` packages Corollary 5.5 — content outside this chunk's own chapter portion
--   (Chapter 5, mission II) — as an explicit hypothesis, per this series' convention.
--   `hwwta_of_load` packages this chunk's own Theorem 11.6 (goal) and Theorem 11.5 (milestone)
--   together, since the corollary's actual new content is deriving `PolicyStable wwta` from the
--   combination of `hnecessary`, `hwwta_of_load`, and `hex`, not re-proving those two theorems.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 221, Corollary 11.7

import Mathlib
import Definitions.Def_ProcessingNetworks_TaskAllocation_TaskAllocationModel
import Definitions.Def_ProcessingNetworks_TaskAllocation_FluidModel

namespace ProcessingNetworks.TaskAllocation

/-- Corollary 11.7, Dai & Harrison p. 221 (PDF p. 237): the WWTA routing policy is maximally
stable in the following sense: if there exists any simply structured routing policy under which
the task allocation model is stable, then it is stable under WWTA. A control policy is represented
abstractly by a value of `Policy`, with `PolicyStable p` recording that the task allocation model
(for the fixed data `dat`) is stable under policy `p` (i.e. its ambient Markov chain is positive
recurrent, `PositiveRecurrent`, Section 11.4). `hnecessary` packages Corollary 5.5 (stability under
any policy implies subcriticality, here in this model's own Lemma 11.2 form) — content structurally
outside this chunk's own chapter portion (Chapter 5, mission II), per this series' convention.
`hwwta_of_load` packages Theorem 11.6 (this chunk's own goal) composed with Theorem 11.5 (this
chunk's own milestone): the load condition (11.4)-(11.5) gives a stable WWTA fluid model, hence
(via Theorem 11.4's bridge from fluid limits to fluid model solutions, and Theorem 11.5's bridge
from fluid limit stability to positive recurrence) a stable ambient chain under WWTA. -/
theorem wwta_maximally_stable
    {L K : ℕ} [Nonempty (Fin K)] (dat : TaskAllocationData L K)
    {Policy : Type*} (PolicyStable : Policy → Prop) (wwta : Policy)
    (hnecessary : (∃ p, PolicyStable p) →
      ∃ lam : Fin L → Fin K → ℝ, (∀ ℓ k, 0 ≤ lam ℓ k) ∧
        (∀ ℓ, ∑ k, lam ℓ k = dat.nu ℓ) ∧ (∀ k, ∑ ℓ, dat.m ℓ k * lam ℓ k < 1))
    (hwwta_of_load : WWTAFluidStable dat → PolicyStable wwta)
    (hex : ∃ p, PolicyStable p) :
    PolicyStable wwta := by sorry

end ProcessingNetworks.TaskAllocation

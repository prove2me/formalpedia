-- Prove2me | Theorems.Thm_ProcessingNetworks_Subcriticality_stable_for_all_subcritical_implies_maximally_stable
-- name    : ProcessingNetworks.Subcriticality.stable_for_all_subcritical_implies_maximally_stable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:29:50.92543+00:00
-- url     : https://prove2.me/theorems/d7c30fae-e2f5-4a05-884e-9f99d2d6b515
-- title:
--   Corollary 5.6 — stability on the whole subcritical region gives maximal stability
-- statement:
--   **Corollary 5.6.** For a given SPN, consider a control policy whose implementation does not
--   depend on the arrival-rate vector $\lambda$. If the policy is stable for every $\lambda$ in the
--   subcritical region $\Lambda$, then it is maximally stable (stable for every $\lambda$ in the
--   possibly-larger stability region $\Lambda^\ast$).
--
--   The book calls this "immediate from Theorem 5.2": since Theorem 5.2 shows $\Lambda^\ast \subset
--   \Lambda$ (no stable policy can exist outside the subcritical region), a policy stable on all of
--   $\Lambda$ is automatically stable on the smaller set $\Lambda^\ast$, which is exactly maximal
--   stability. Corollary 5.6 is the basis for every later maximal-stability proof in the book
--   (Chapters 6-14): each exhibits a $\lambda$-independent policy and shows it is stable throughout
--   the subcritical region, then invokes this corollary rather than re-establishing $\Lambda^\ast
--   \subset \Lambda$ each time.
--
--   **Formalization note.** `hΛstar_subset_Λ` makes the "immediate from Theorem 5.2" step an
--   explicit hypothesis (`StabilityRegion PolicyStable ⊆ SubcriticalRegion D`) rather than an
--   internal derivation, since deriving it afresh here would just restate
--   `subcriticality_necessary_for_stability`; a fully assembled proof would discharge it by that
--   goal theorem.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 103, Corollary 5.6

import Mathlib
import Definitions.Def_ProcessingNetworks_Subcriticality_SPNPlanningData
import Definitions.Def_ProcessingNetworks_Subcriticality_StaticPlanningProblem
import Definitions.Def_ProcessingNetworks_Subcriticality_MaximalStability

namespace ProcessingNetworks.Subcriticality

/-- Corollary 5.6, p. 103 (PDF p. 119): for a given SPN, consider a control policy whose
implementation does not depend on `λ`. If the policy is stable for all `λ ∈ Λ`, then it is
maximally stable. `hΛstar_subset_Λ` records the "immediate from Theorem 5.2" step: the stability
region `Λ*` is contained in the subcritical region `Λ` (Theorem 5.2's own conclusion, restated as
a subset relation), the fact from which the book calls this corollary "immediate." -/
theorem stable_for_all_subcritical_implies_maximally_stable
    {I J K : ℕ} {Policy : Type*} (D : SPNPlanningData I J K)
    (PolicyStable : Policy → (Fin I → ℝ) → Prop)
    (hΛstar_subset_Λ : StabilityRegion PolicyStable ⊆ SubcriticalRegion D)
    (p : Policy) (hp : ∀ lam ∈ SubcriticalRegion D, PolicyStable p lam) :
    IsMaximallyStable PolicyStable p := by sorry

end ProcessingNetworks.Subcriticality

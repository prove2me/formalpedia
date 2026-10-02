-- Prove2me | Theorems.Thm_ProcessingNetworks_PacketNetworks_subcritical_lt_hull_image
-- name    : ProcessingNetworks.PacketNetworks.subcritical_lt_hull_image
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:49:51.809977+00:00
-- url     : https://prove2.me/theorems/14750acb-b17b-44cb-94a7-fcea7bf23359
-- title:
--   Proposition 12.9 — a necessary condition for subcriticality via ⟨S⟩ (milestone)
-- statement:
--   **Proposition 12.9.** If $\lambda\in\Lambda$, then $\lambda < R\hat s$ for some $\hat s\in
--   \langle S\rangle$ (Eq. 12.26).
--
--   The book's own proof constructs $\hat s$ explicitly from a processing plan for each class,
--   perturbing a feasible $x$ along the all-classes-exit direction $\tilde s := s_1+\dots+s_I$.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 234, Proposition 12.9, Eq. (12.26)

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_SubcriticalRegion

namespace ProcessingNetworks.PacketNetworks

/-- Proposition 12.9, Dai & Harrison p. 234 (PDF p. 250): if `λ ∈ Λ`, then `λ < Rŝ` for some
`ŝ ∈ ⟨S⟩` (Eq. 12.26) — a necessary condition for subcriticality stated purely in terms of the
schedule hull, with no reference to the underlying link configurations. -/
theorem subcritical_lt_hull_image
    {I J K : ℕ} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ)) (cfg : LinkConfigData J K)
    (lam : Fin I → ℝ) (hlam : lam ∈ subcriticalRegion dat S cfg) :
    ∃ shat ∈ hullFinset S, ∀ i, lam i < (R dat).mulVec shat i := by sorry

end ProcessingNetworks.PacketNetworks

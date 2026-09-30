-- Prove2me | Theorems.Thm_RamadgeWonham_Quotient_prop_8_1_iv
-- name    : RamadgeWonham.Quotient.prop_8_1_iv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:43:43.502772+00:00
-- url     : https://prove2.me/theorems/4b1070b2-b8c8-4a4d-a1bd-dc69d80df271
-- title:
--   Proposition 8.1 (iv), p. 219 — a projection preserves nonblocking, nonrejecting and proper
-- statement:
--   Let $\mathcal G$ be a trim generator over a finite alphabet $\Sigma$ with controllable events $\Sigma_c$. Let $\mathcal S$ and $\hat{\mathcal S}$ be supervisors with accessible automata, let $\mathcal S$ be complete with respect to $\mathcal G$, and let $\pi : \mathcal S \to \hat{\mathcal S}$ be a projection. Then
--
--   1. $\mathcal S$ is nonblocking iff $\hat{\mathcal S}$ is nonblocking;
--   2. $\mathcal S$ is nonrejecting iff $\hat{\mathcal S}$ is nonrejecting;
--   3. $\mathcal S$ is proper iff $\hat{\mathcal S}$ is proper.
--
--   **Formalization Note** Standing assumptions as hypotheses: $\Sigma$ finite, $\mathcal G$ trim, both supervisor automata accessible.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 219, Proposition 8.1 (iv)

import Mathlib
import Definitions.Def_RamadgeWonham_Quotient_Projection

namespace RamadgeWonham.Quotient

open Shared.Generator

/-- Proposition 8.1 (iv) (p. 219): if `𝒮` is complete with respect to `𝒢` and `π : 𝒮 → 𝒮̂` is a
projection, then `𝒮` is nonblocking (respectively, nonrejecting, proper) iff `𝒮̂` is nonblocking
(respectively, nonrejecting, proper). -/
theorem prop_8_1_iv
    {α : Type} [Fintype α] {Ec : Set α} (𝒢 : Shared.Generator α) (h𝒢 : 𝒢.L = Shared.pre 𝒢.Lm)
    (𝒮 𝒮h : Shared.Supervisor α Ec) (h𝒮acc : 𝒮.S.Accessible) (h𝒮hacc : 𝒮h.S.Accessible)
    (h𝒮 : Shared.Complete 𝒢 𝒮)
    (π : 𝒮.S.Q → 𝒮h.S.Q) (hπ : IsProjection 𝒮 𝒮h π) :
    (Shared.Nonblocking 𝒢 𝒮 ↔ Shared.Nonblocking 𝒢 𝒮h) ∧ (Shared.Nonrejecting 𝒢 𝒮 ↔ Shared.Nonrejecting 𝒢 𝒮h) ∧
      (Shared.Proper 𝒢 𝒮 ↔ Shared.Proper 𝒢 𝒮h) := by sorry

end RamadgeWonham.Quotient

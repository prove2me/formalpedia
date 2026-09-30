-- Prove2me | Theorems.Thm_RamadgeWonham_Quotient_prop_8_1_iii
-- name    : RamadgeWonham.Quotient.prop_8_1_iii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:43:06.013319+00:00
-- url     : https://prove2.me/theorems/36a0e10c-c74d-4ee2-91d9-1177fd72266f
-- title:
--   Proposition 8.1 (iii), p. 219 — the quotient of a complete supervisor is complete
-- statement:
--   Let $\mathcal G$ be a trim generator over a finite alphabet $\Sigma$ with controllable events $\Sigma_c$. Let $\mathcal S$ and $\hat{\mathcal S}$ be supervisors with accessible automata, let $\mathcal S$ be complete with respect to $\mathcal G$, and let $\pi : \mathcal S \to \hat{\mathcal S}$ be a projection. Then
--   $$\hat{\mathcal S} \text{ is complete with respect to } \mathcal G.$$
--
--   **Formalization Note** Standing assumptions as hypotheses: $\Sigma$ finite, $\mathcal G$ trim, both supervisor automata accessible.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 219, Proposition 8.1 (iii)

import Mathlib
import Definitions.Def_RamadgeWonham_Quotient_Projection

namespace RamadgeWonham.Quotient

open Shared.Generator

/-- Proposition 8.1 (iii) (p. 219): if `𝒮` is complete with respect to `𝒢` and `π : 𝒮 → 𝒮̂` is a
projection, then `𝒮̂` is complete with respect to `𝒢`. -/
theorem prop_8_1_iii
    {α : Type} [Fintype α] {Ec : Set α} (𝒢 : Shared.Generator α) (h𝒢 : 𝒢.L = Shared.pre 𝒢.Lm)
    (𝒮 𝒮h : Shared.Supervisor α Ec) (h𝒮acc : 𝒮.S.Accessible) (h𝒮hacc : 𝒮h.S.Accessible)
    (h𝒮 : Shared.Complete 𝒢 𝒮)
    (π : 𝒮.S.Q → 𝒮h.S.Q) (hπ : IsProjection 𝒮 𝒮h π) :
    Shared.Complete 𝒢 𝒮h := by sorry

end RamadgeWonham.Quotient

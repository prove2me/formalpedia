-- Prove2me | Theorems.Thm_RamadgeWonham_Quotient_prop_8_1_ii
-- name    : RamadgeWonham.Quotient.prop_8_1_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:42:08.845342+00:00
-- url     : https://prove2.me/theorems/768dfaf5-292e-498f-a800-3310438bee20
-- title:
--   Proposition 8.1 (ii), p. 219 — a projection preserves (L_m, L_c, L)(𝒮/𝒢)
-- statement:
--   Let $\mathcal G$ be a trim generator over a finite alphabet $\Sigma$ with controllable events $\Sigma_c$. Let $\mathcal S$ and $\hat{\mathcal S}$ be supervisors with accessible automata, let $\mathcal S$ be complete with respect to $\mathcal G$, and let $\pi : \mathcal S \to \hat{\mathcal S}$ be a projection. Then
--   $$\big(L_m, L_c, L\big)(\mathcal S/\mathcal G) = \big(L_m, L_c, L\big)(\hat{\mathcal S}/\mathcal G),$$
--   that is, the marked, controlled and generated languages of the two closed loops coincide.
--
--   A projection therefore replaces a supervisor by a smaller one with exactly the same closed-loop behaviour.
--
--   **Formalization Note** Standing assumptions as hypotheses: $\Sigma$ finite, $\mathcal G$ trim, both supervisor automata accessible.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 219, Proposition 8.1 (ii)

import Mathlib
import Definitions.Def_RamadgeWonham_Quotient_Projection

namespace RamadgeWonham.Quotient

open Shared.Generator

/-- Proposition 8.1 (ii) (p. 219): if `𝒮` is complete with respect to `𝒢` and `π : 𝒮 → 𝒮̂` is a
projection, then `(L_m, L_c, L)(𝒮/𝒢) = (L_m, L_c, L)(𝒮̂/𝒢)`. -/
theorem prop_8_1_ii
    {α : Type} [Fintype α] {Ec : Set α} (𝒢 : Shared.Generator α) (h𝒢 : 𝒢.L = Shared.pre 𝒢.Lm)
    (𝒮 𝒮h : Shared.Supervisor α Ec) (h𝒮acc : 𝒮.S.Accessible) (h𝒮hacc : 𝒮h.S.Accessible)
    (h𝒮 : Shared.Complete 𝒢 𝒮)
    (π : 𝒮.S.Q → 𝒮h.S.Q) (hπ : IsProjection 𝒮 𝒮h π) :
    Shared.Lmsup 𝒢 𝒮 = Shared.Lmsup 𝒢 𝒮h ∧ Shared.Lcsup 𝒢 𝒮 = Shared.Lcsup 𝒢 𝒮h ∧ Shared.Lsup 𝒢 𝒮 = Shared.Lsup 𝒢 𝒮h := by sorry

end RamadgeWonham.Quotient

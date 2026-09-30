-- Prove2me | Theorems.Thm_RamadgeWonham_Quotient_prop_8_1_i
-- name    : RamadgeWonham.Quotient.prop_8_1_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:41:09.980596+00:00
-- url     : https://prove2.me/theorems/0112580a-4542-4db7-bdd9-4e9681eb60ae
-- title:
--   Proposition 8.1 (i), p. 219 — a projection from a complete supervisor is unique
-- statement:
--   Let $\mathcal G$ be a trim generator over a finite alphabet $\Sigma$ with controllable events $\Sigma_c$. Let $\mathcal S = (S, \phi)$ and $\hat{\mathcal S} = (\hat S, \hat \phi)$ be supervisors with accessible automata $S$, $\hat S$, and let $\mathcal S$ be complete with respect to $\mathcal G$. If $\pi, \pi' : X \to \hat X$ are both projections $\mathcal S \to \hat{\mathcal S}$, then
--   $$\pi = \pi'.$$
--
--   So the quotient relation between supervisors carries no choice: a projection, when it exists, is determined by the two supervisors.
--
--   **Formalization Note** The standing assumptions of the paper are hypotheses: $\Sigma$ finite (p. 207), $\mathcal G$ trim, i.e. $L(\mathcal G) = \bar L_m(\mathcal G)$ (pp. 212–213), and both supervisor automata accessible (p. 210, recalled on p. 219).
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 219, Proposition 8.1 (i)

import Mathlib
import Definitions.Def_RamadgeWonham_Quotient_Projection

namespace RamadgeWonham.Quotient

open Shared.Generator

/-- Proposition 8.1 (i) (p. 219): if `𝒮` is complete with respect to `𝒢` and `π : 𝒮 → 𝒮̂` is a
projection, then `π` is unique. -/
theorem prop_8_1_i
    {α : Type} [Fintype α] {Ec : Set α} (𝒢 : Shared.Generator α) (h𝒢 : 𝒢.L = Shared.pre 𝒢.Lm)
    (𝒮 𝒮h : Shared.Supervisor α Ec) (h𝒮acc : 𝒮.S.Accessible) (h𝒮hacc : 𝒮h.S.Accessible)
    (h𝒮 : Shared.Complete 𝒢 𝒮)
    (π π' : 𝒮.S.Q → 𝒮h.S.Q) (hπ : IsProjection 𝒮 𝒮h π) (hπ' : IsProjection 𝒮 𝒮h π') :
    π = π' := by sorry

end RamadgeWonham.Quotient

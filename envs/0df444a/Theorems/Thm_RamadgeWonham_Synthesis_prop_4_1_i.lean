-- Prove2me | Theorems.Thm_RamadgeWonham_Synthesis_prop_4_1_i
-- name    : RamadgeWonham.Synthesis.prop_4_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:38:33.474372+00:00
-- url     : https://prove2.me/theorems/48aa3811-ec3f-4044-9c9e-7af3537dfec6
-- title:
--   Proposition 4.1 (i), p. 212 — every K ⊆ L_m(𝒢) is marked by a complete supervisor with L(𝒮/𝒢) = L(𝒢)
-- statement:
--   Let $\mathcal G$ be a generator over a finite alphabet $\Sigma$ with controllable events $\Sigma_c$, and assume $\mathcal G$ is trim in the sense $L(\mathcal G) = \bar L_m(\mathcal G)$. For each sublanguage $K \subseteq L_m(\mathcal G)$ there is a complete supervisor $\mathcal S$ (with accessible automaton) such that
--
--   $$L(\mathcal S/\mathcal G) = L(\mathcal G), \qquad L_m(\mathcal S/\mathcal G) = K.$$
--
--   This expresses that marking is independent of control: any set of plant tasks can be recorded without restricting the plant at all.
--
--   **Formalization Note.** The standing assumptions of the paper (finite alphabet, $L(\mathcal G) = \bar L_m(\mathcal G)$ from §4, accessible supervisor automaton) are explicit hypotheses and conjuncts.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 212, Proposition 4.1 (i)

import Mathlib
import Definitions.Def_RamadgeWonham_Shared_Supervisor

namespace RamadgeWonham.Synthesis

/-- Ramadge–Wonham 1987, Proposition 4.1 (i), p. 212. Standing assumptions: `Σ` finite (p. 207),
`𝒢` trim, `L(𝒢) = L̄_m(𝒢)` (§4, p. 212), supervisors accessible (p. 210). For each sublanguage
`K ⊆ L_m(𝒢)` there is a complete supervisor `𝒮` with `L(𝒮/𝒢) = L(𝒢)` and `L_m(𝒮/𝒢) = K`. -/
theorem prop_4_1_i {α : Type} [Fintype α] (G : Shared.Generator α) (Ec : Set α)
    (hG : G.L = Shared.pre G.Lm) (K : Set (List α)) (hK : K ⊆ G.Lm) :
    ∃ 𝒮 : Shared.Supervisor α Ec, 𝒮.S.Accessible ∧ Shared.Complete G 𝒮 ∧
      Shared.Lsup G 𝒮 = G.L ∧ Shared.Lmsup G 𝒮 = K := by sorry

end RamadgeWonham.Synthesis

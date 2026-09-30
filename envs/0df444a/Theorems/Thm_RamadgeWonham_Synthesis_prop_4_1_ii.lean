-- Prove2me | Theorems.Thm_RamadgeWonham_Synthesis_prop_4_1_ii
-- name    : RamadgeWonham.Synthesis.prop_4_1_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:39:07.109781+00:00
-- url     : https://prove2.me/theorems/7ce29a60-b8c2-4a7a-a50d-125383a944e6
-- title:
--   Proposition 4.1 (ii), p. 212 — any K ⊆ L ∩ L_m(𝒢) is marked by a complete supervisor keeping L(𝒮_K/𝒢) = L
-- statement:
--   Let $\mathcal G$ be a generator over a finite alphabet with controllable events $\Sigma_c$ and $L(\mathcal G) = \bar L_m(\mathcal G)$. Let $L \subseteq L(\mathcal G)$ be closed. If there is a complete supervisor $\mathcal S$ with $L(\mathcal S/\mathcal G) = L$, then for every $K \subseteq L \cap L_m(\mathcal G)$ there is a complete supervisor $\mathcal S_K$ with
--
--   $$L(\mathcal S_K/\mathcal G) = L, \qquad L_m(\mathcal S_K/\mathcal G) = K.$$
--
--   Once a closed-loop language is achievable, every marking task consistent with it is achievable too.
--
--   **Formalization Note.** All supervisors (hypothesis and conclusion) have accessible automata, the paper's standing assumption.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 212, Proposition 4.1 (ii)

import Mathlib
import Definitions.Def_RamadgeWonham_Shared_Supervisor

namespace RamadgeWonham.Synthesis

/-- Ramadge–Wonham 1987, Proposition 4.1 (ii), p. 212. Standing assumptions: `Σ` finite (p. 207),
`L(𝒢) = L̄_m(𝒢)` (§4, p. 212), supervisors accessible (p. 210). Let `L ⊆ L(𝒢)` be closed. If some
complete supervisor `𝒮` has `L(𝒮/𝒢) = L`, then for every `K ⊆ L ∩ L_m(𝒢)` there is a complete
supervisor `𝒮_K` with `L(𝒮_K/𝒢) = L` and `L_m(𝒮_K/𝒢) = K`. -/
theorem prop_4_1_ii {α : Type} [Fintype α] (G : Shared.Generator α) (Ec : Set α)
    (hG : G.L = Shared.pre G.Lm) (L : Set (List α)) (hLcl : Shared.IsClosedLang L) (hLG : L ⊆ G.L)
    (hS : ∃ 𝒮 : Shared.Supervisor α Ec, 𝒮.S.Accessible ∧ Shared.Complete G 𝒮 ∧ Shared.Lsup G 𝒮 = L)
    (K : Set (List α)) (hK : K ⊆ L ∩ G.Lm) :
    ∃ 𝒮K : Shared.Supervisor α Ec, 𝒮K.S.Accessible ∧ Shared.Complete G 𝒮K ∧
      Shared.Lsup G 𝒮K = L ∧ Shared.Lmsup G 𝒮K = K := by sorry

end RamadgeWonham.Synthesis

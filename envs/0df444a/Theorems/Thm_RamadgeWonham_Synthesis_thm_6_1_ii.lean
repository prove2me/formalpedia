-- Prove2me | Theorems.Thm_RamadgeWonham_Synthesis_thm_6_1_ii
-- name    : RamadgeWonham.Synthesis.thm_6_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:41:01.85815+00:00
-- url     : https://prove2.me/theorems/376dbf50-dee5-48b6-b67f-f7fad0dc8be1
-- title:
--   Theorem 6.1 (ii), p. 216 — a proper supervisor with L_c(𝒮/𝒢) = K exists iff K is controllable and L_m(𝒢)-closed
-- statement:
--   Let $\mathcal G$ be a generator over a finite alphabet with controllable events $\Sigma_c$ and $L(\mathcal G) = \bar L_m(\mathcal G)$. Let $K \subseteq L_m(\mathcal G)$ with $K \neq \emptyset$. There exists a proper supervisor $\mathcal S$ (with accessible automaton) with
--
--   $$L_c(\mathcal S/\mathcal G) = K$$
--
--   if and only if $K$ is controllable and $L_m(\mathcal G)$-closed, that is, $K = \bar K \cap L_m(\mathcal G)$.
--
--   This is the counterpart of Theorem 6.1 (i) for the controlled language $L_c(\mathcal S/\mathcal G) = L(\mathcal S/\mathcal G) \cap L_m(\mathcal G)$.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 216, Theorem 6.1 (ii)

import Mathlib
import Definitions.Def_RamadgeWonham_Shared_Supervisor
import Definitions.Def_RamadgeWonham_Synthesis_Controllable

namespace RamadgeWonham.Synthesis

/-- Ramadge–Wonham 1987, Theorem 6.1 (ii), p. 216. Standing assumptions: `Σ` finite (p. 207),
`L(𝒢) = L̄_m(𝒢)` (§5, p. 213), supervisors accessible (p. 210). Let `K ⊆ L_m(𝒢)`, `K ≠ ∅`.
There is a proper supervisor `𝒮` with `L_c(𝒮/𝒢) = K` iff `K` is controllable and
`L_m(𝒢)`-closed (`K = K̄ ∩ L_m(𝒢)`). -/
theorem thm_6_1_ii {α : Type} [Fintype α] (G : Shared.Generator α) (Ec : Set α)
    (hG : G.L = Shared.pre G.Lm) (K : Set (List α)) (hK : K ⊆ G.Lm) (hKne : K.Nonempty) :
    (∃ 𝒮 : Shared.Supervisor α Ec, 𝒮.S.Accessible ∧ Shared.Proper G 𝒮 ∧ Shared.Lcsup G 𝒮 = K) ↔
      (Controllable G Ec K ∧ LClosed G.Lm K) := by sorry

end RamadgeWonham.Synthesis

-- Prove2me | Theorems.Thm_RamadgeWonham_Synthesis_thm_6_1_i
-- name    : RamadgeWonham.Synthesis.thm_6_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:40:35.386021+00:00
-- url     : https://prove2.me/theorems/33d8529e-7be5-4aa0-9e4b-57872cee8970
-- title:
--   Theorem 6.1 (i), p. 216 — a proper supervisor with L_m(𝒮/𝒢) = K exists iff K is controllable; then L_c = L_m(𝒢) ∩ K̄
-- statement:
--   Let $\mathcal G$ be a generator over a finite alphabet with controllable events $\Sigma_c$ and $L(\mathcal G) = \bar L_m(\mathcal G)$. Let $K \subseteq L_m(\mathcal G)$ with $K \neq \emptyset$. Then there exists a proper supervisor $\mathcal S$ (with accessible automaton) with $L_m(\mathcal S/\mathcal G) = K$ if and only if $K$ is controllable. Moreover, in that case every such proper supervisor satisfies
--
--   $$L_c(\mathcal S/\mathcal G) = L_m(\mathcal G) \cap \bar K.$$
--
--   This is the existence theorem for supervisors that realize a prescribed marked behaviour without blocking.
--
--   **Formalization Note.** The paper's "In that case" is formalized for every proper supervisor with accessible automaton and $L_m(\mathcal S/\mathcal G) = K$, which is the stronger reading and holds because properness forces $L(\mathcal S/\mathcal G) = \bar K$.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 216, Theorem 6.1 (i)

import Mathlib
import Definitions.Def_RamadgeWonham_Shared_Supervisor
import Definitions.Def_RamadgeWonham_Synthesis_Controllable

namespace RamadgeWonham.Synthesis

/-- Ramadge–Wonham 1987, Theorem 6.1 (i), p. 216. Standing assumptions: `Σ` finite (p. 207),
`L(𝒢) = L̄_m(𝒢)` (§5, p. 213), supervisors accessible (p. 210). Let `K ⊆ L_m(𝒢)`, `K ≠ ∅`.
There is a proper supervisor `𝒮` with `L_m(𝒮/𝒢) = K` iff `K` is controllable; and in that case
(for every such `𝒮`) `L_c(𝒮/𝒢) = L_m(𝒢) ∩ K̄`. -/
theorem thm_6_1_i {α : Type} [Fintype α] (G : Shared.Generator α) (Ec : Set α)
    (hG : G.L = Shared.pre G.Lm) (K : Set (List α)) (hK : K ⊆ G.Lm) (hKne : K.Nonempty) :
    ((∃ 𝒮 : Shared.Supervisor α Ec, 𝒮.S.Accessible ∧ Shared.Proper G 𝒮 ∧ Shared.Lmsup G 𝒮 = K) ↔
        Controllable G Ec K) ∧
      ∀ 𝒮 : Shared.Supervisor α Ec, 𝒮.S.Accessible → Shared.Proper G 𝒮 → Shared.Lmsup G 𝒮 = K →
        Shared.Lcsup G 𝒮 = G.Lm ∩ Shared.pre K := by sorry

end RamadgeWonham.Synthesis

-- Prove2me | Theorems.Thm_RamadgeWonham_Synthesis_prop_5_1
-- name    : RamadgeWonham.Synthesis.prop_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:39:47.628611+00:00
-- url     : https://prove2.me/theorems/d2f7bf15-7fd8-4a11-b97d-07c46249e1dd
-- title:
--   Proposition 5.1, p. 214 — a complete supervisor realizes (K₁, K₂, K₃) iff K₁ ⊆ K₂, K₂ = K₃ ∩ L_m(𝒢), K₃ closed and controllable
-- statement:
--   Let $\mathcal G$ be a generator over a finite alphabet with controllable events $\Sigma_c$ and $L(\mathcal G) = \bar L_m(\mathcal G)$. Let $K_1 \subseteq L_m(\mathcal G)$, $K_2 \subseteq L_m(\mathcal G)$ and $K_3 \subseteq L(\mathcal G)$ with $K_3 \neq \emptyset$. There exists a complete supervisor $\mathcal S$ (with accessible automaton) such that
--
--   $$L_m(\mathcal S/\mathcal G) = K_1, \qquad L_c(\mathcal S/\mathcal G) = K_2, \qquad L(\mathcal S/\mathcal G) = K_3$$
--
--   if and only if
--
--   1. $K_1 \subseteq K_2$,
--   2. $K_2 = K_3 \cap L_m(\mathcal G)$,
--   3. $K_3$ is closed and controllable.
--
--   This characterizes exactly which triples of closed-loop languages complete supervisors can realize, and is the technical basis of Theorems 6.1 and 7.1.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 214, Proposition 5.1, display (5.1)

import Mathlib
import Definitions.Def_RamadgeWonham_Shared_Supervisor
import Definitions.Def_RamadgeWonham_Synthesis_Controllable

namespace RamadgeWonham.Synthesis

/-- Ramadge–Wonham 1987, Proposition 5.1, p. 214. Standing assumptions: `Σ` finite (p. 207),
`L(𝒢) = L̄_m(𝒢)` (§5, p. 213), supervisors accessible (p. 210). Let `K₁ ⊆ L_m(𝒢)`,
`K₂ ⊆ L_m(𝒢)`, `K₃ ⊆ L(𝒢)`, `K₃ ≠ ∅`. There is a complete supervisor `𝒮` with
`L_m(𝒮/𝒢) = K₁`, `L_c(𝒮/𝒢) = K₂`, `L(𝒮/𝒢) = K₃` iff (i) `K₁ ⊆ K₂`, (ii) `K₂ = K₃ ∩ L_m(𝒢)`,
(iii) `K₃` is closed and controllable. -/
theorem prop_5_1 {α : Type} [Fintype α] (G : Shared.Generator α) (Ec : Set α)
    (hG : G.L = Shared.pre G.Lm) (K₁ K₂ K₃ : Set (List α))
    (hK₁ : K₁ ⊆ G.Lm) (hK₂ : K₂ ⊆ G.Lm) (hK₃ : K₃ ⊆ G.L) (hK₃ne : K₃.Nonempty) :
    (∃ 𝒮 : Shared.Supervisor α Ec, 𝒮.S.Accessible ∧ Shared.Complete G 𝒮 ∧
        Shared.Lmsup G 𝒮 = K₁ ∧ Shared.Lcsup G 𝒮 = K₂ ∧ Shared.Lsup G 𝒮 = K₃) ↔
      (K₁ ⊆ K₂ ∧ K₂ = K₃ ∩ G.Lm ∧ Shared.IsClosedLang K₃ ∧ Controllable G Ec K₃) := by sorry

end RamadgeWonham.Synthesis

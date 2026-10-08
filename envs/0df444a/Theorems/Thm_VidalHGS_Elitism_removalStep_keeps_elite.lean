-- Prove2me | Theorems.Thm_VidalHGS_Elitism_removalStep_keeps_elite
-- name    : VidalHGS.Elitism.removalStep_keeps_elite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T14:25:17.381978+00:00
-- url     : https://prove2.me/theorems/f3250448-9b9f-4b4a-938b-529a1cdc6555
-- title:
--   p. 17, Section 4.6, proof of the Proposition — one removal step spares an elite individual outside X
-- statement:
--   Let $P$ be a subpopulation, $\mathit{nbElit} + 1 \le |P|$, and let $Q$ arise from $P$ by one removal step of the survivor-selection procedure (remove an individual of maximum Biased Fitness in $X(P)$ if $X(P) \neq \emptyset$, otherwise in $P$). If $J \in P$, $J \notin X(P)$, and $J$ is among the $\mathit{nbElit}$ best individuals of $P$ in terms of fitness, then
--   $$J \in Q.$$
--
--   This is the last sentence of the proof of the elitism Proposition. When $X(P) = \emptyset$, the removed individual has Biased Fitness at least that of the worst individual, hence at least $1$, while $BF_P(J) < 1$. When $X(P) \ne \emptyset$, the removed individual lies in $X(P)$ and $J$ does not — this case is why the Proposition assumes $J \notin X$.
--
--   **Formalization Note.** The paper's sentence covers the case $X = \emptyset$; the case $X \neq \emptyset$ is part of the same step of the procedure and is included here. The condition $\mathit{nbElit} \le |P| - 1$ is the population-size condition implicit in the paper (Table 1 and Section 4.6).
-- source:
--   Vidal, Crainic, Gendreau, Lahrichi and Rei, A Hybrid Genetic Algorithm for Multi-Depot and Periodic Vehicle Routing Problems, CIRRELT-2010-34 (July 2010), p. 17, Section 4.6, proof of the Proposition (third sentence)

import Mathlib
import Definitions.Def_VidalHGS_Elitism_SurvivorSelection

namespace VidalHGS.Elitism

/-- Section 4.6, p. 17, proof of the Proposition: one removal step of the survivor-selection
procedure does not remove an individual `J ∉ X` that is among the `nbElit` best in terms of
fitness, provided `nbElit ≤ nbIndiv − 1`. -/
theorem removalStep_keeps_elite {α : Type*} [DecidableEq α]
    (c : α → ℝ) (δ : α → α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ) (best : α)
    (P Q : Finset α) (J : α)
    (hstep : RemovalStep c δ Δ nbElit best P Q) (hsize : nbElit + 1 ≤ P.card)
    (hJ : J ∈ P) (hJX : J ∉ cloneSet c δ best P) (helite : IsElite c nbElit P J) :
    J ∈ Q := by sorry

end VidalHGS.Elitism

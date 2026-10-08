-- Prove2me | Theorems.Thm_VidalHGS_Elitism_elite_not_removed
-- name    : VidalHGS.Elitism.elite_not_removed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T14:24:49.517669+00:00
-- url     : https://prove2.me/theorems/7e8ea484-0211-4775-a0dd-b245a1b70530
-- title:
--   Section 4.6, Proposition — Biased-Fitness survivor selection never removes an elite individual outside X
-- statement:
--   Consider one subpopulation $P$ of the hybrid genetic algorithm HGSADC, with costs $c$, distance $\delta$, diversity contribution $\Delta$, elite parameter $\mathit{nbElit}$, and current best solution $\mathit{best}$. The survivor-selection procedure removes $\lambda$ individuals one at a time; at each step it recomputes the ranks, the Biased Fitness $BF$ and the set $X$ of non-best individuals having a clone on the current population, and removes an individual of maximum $BF$ from $X$ if $X \neq \emptyset$, and from the whole population otherwise.
--
--   Suppose $\mathit{nbElit} + \lambda \le |P|$. If $J \in P$, $J \notin X(P)$, and $J$ is among the $\mathit{nbElit}$ best individuals of $P$ in terms of fitness (fewer than $\mathit{nbElit}$ members of $P$ have strictly smaller cost), then for every run of the procedure from $P$ to the final population $P'$,
--   $$J \in P'.$$
--
--   In the paper's words: using the Biased Fitness function, an individual $I \notin X$ that is part of the $\mathit{nbElit}$ best individuals of the subpopulation in terms of fitness will not be removed by the survivor-selection procedure. This is the elitism guarantee that justifies the parameter $\mathit{nbElit}$ in the Biased Fitness (7).
--
--   **Formalization Note.** The number $\lambda$ of removals is called `nOff` in Lean. The hypothesis $\mathit{nbElit} + \lambda \le |P|$ is not written in the Proposition; it comes from the paper's setting (Section 4.6: a subpopulation of $\mu + \lambda$ individuals is reduced to $\mu$; Table 1: $\mathit{nbElit} = el \times \mu$ with $el \in [0, 1]$), and without it the statement is false. The conclusion holds for every run, whatever tie-breaking is used in the maximum. The diversity contribution is an arbitrary function of (population, individual), which includes the paper's (5). The best solution is a parameter and need not belong to $P$ (for the infeasible subpopulation it is the incumbent feasible solution); $J$ may itself be the best solution.
-- source:
--   Vidal, Crainic, Gendreau, Lahrichi and Rei, A Hybrid Genetic Algorithm for Multi-Depot and Periodic Vehicle Routing Problems, CIRRELT-2010-34 (July 2010), pp. 16–17, Section 4.6, Proposition; size condition from p. 16 and Table 1, p. 20

import Mathlib
import Definitions.Def_VidalHGS_Elitism_SurvivorSelection

namespace VidalHGS.Elitism

/-- Section 4.6, pp. 16–17, Proposition: using the Biased Fitness function, an individual
`J ∉ X` that is part of the `nbElit` best individuals of the subpopulation `P` in terms of
fitness is not removed by the survivor-selection procedure, which removes `nOff` (the paper's
`λ`) individuals, provided `nbElit + nOff ≤ |P|` (Table 1: `nbElit = el × μ ≤ μ`, and the
procedure reduces `μ + λ` individuals to `μ`). -/
theorem elite_not_removed {α : Type*} [DecidableEq α]
    (c : α → ℝ) (δ : α → α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ) (best : α)
    (nOff : ℕ) (P P' : Finset α) (J : α)
    (hrun : SurvivorRun c δ Δ nbElit best nOff P P') (hsize : nbElit + nOff ≤ P.card)
    (hJ : J ∈ P) (hJX : J ∉ cloneSet c δ best P) (helite : IsElite c nbElit P J) :
    J ∈ P' := by sorry

end VidalHGS.Elitism

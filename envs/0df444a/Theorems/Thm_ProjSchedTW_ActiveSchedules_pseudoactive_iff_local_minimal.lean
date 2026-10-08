-- Prove2me | Theorems.Thm_ProjSchedTW_ActiveSchedules_pseudoactive_iff_local_minimal
-- name    : ProjSchedTW.ActiveSchedules.pseudoactive_iff_local_minimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T16:05:48.44758+00:00
-- url     : https://prove2.me/theorems/3817a2aa-7e3e-4e28-a0d0-f201322fac59
-- title:
--   §2.4, p. 44 — pseudoactive schedules are exactly the local minimal points of the feasible region
-- statement:
--   A point $S\in\mathcal M\subseteq\mathbb R^{n+2}$ is a *local minimal point* of $\mathcal M$ if there is $\varepsilon>0$ such that $S$ is a minimal point of $\mathcal M\cap N_\varepsilon(S)$, where
--   $$N_\varepsilon(S)=\Bigl\{S'\in\mathbb R^{n+2}\ \Bigm|\ \sqrt{\textstyle\sum_{i\in V}(S'_i-S_i)^2}<\varepsilon\Bigr\}$$
--   is the Euclidean $\varepsilon$-neighbourhood of $S$. Then a schedule $S$ is pseudoactive if and only if it is a local minimal point of the feasible region $\mathcal S$.
--
--   Together with Theorem 2.4.9 (a) and (b), this places the pseudoactive schedules between the global minimal points of $\mathcal S$ (active schedules) and the minimal points of the components of $\mathcal S$ (semiactive schedules) in purely geometric terms.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, §2.4, p. 44, after the proof of Theorem 2.4.9 (local minimal points)

import Mathlib
import Definitions.Def_ProjSchedTW_ActiveSchedules_Project
import Definitions.Def_ProjSchedTW_ActiveSchedules_Shifts

namespace ProjSchedTW.ActiveSchedules

/-- §2.4, p. 44 (after the proof of Theorem 2.4.9): the pseudoactive schedules are exactly the
local minimal points of `𝒮`, i.e. the points `S ∈ 𝒮` that are minimal points of
`𝒮 ∩ N_ε(S)` for some `ε > 0`, where `N_ε(S)` is the open Euclidean `ε`-ball around `S`. -/
theorem pseudoactive_iff_local_minimal {n : ℕ} {K : Type} (P : Project n K)
    (S : Fin (n + 2) → ℝ) :
    IsPseudoactive P S ↔
      ∃ ε : ℝ, 0 < ε ∧
        Minimal (· ∈ feasibleSet P ∩ {S' | Real.sqrt (∑ i, (S' i - S i) ^ 2) < ε}) S := by sorry

end ProjSchedTW.ActiveSchedules

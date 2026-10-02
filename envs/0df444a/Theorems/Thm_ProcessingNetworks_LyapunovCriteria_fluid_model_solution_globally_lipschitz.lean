-- Prove2me | Theorems.Thm_ProcessingNetworks_LyapunovCriteria_fluid_model_solution_globally_lipschitz
-- name    : ProcessingNetworks.LyapunovCriteria.fluid_model_solution_globally_lipschitz
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:57:19.132158+00:00
-- url     : https://prove2.me/theorems/092da691-102b-43db-8cdc-5dc608459047
-- title:
--   Lemma 8.3 — fluid model solutions are globally Lipschitz (milestone)
-- statement:
--   **Lemma 8.3.** Any solution $(D,F,T,Z)$ of the fluid equations (6.1)-(6.6) is globally
--   Lipschitz.
--
--   This is what makes Lemma 8.5's "$f(t) := H(Z(t))$ is Lipschitz" step possible for *any*
--   Lipschitz $H$ and *any* fluid model solution, without needing to verify Lipschitz continuity
--   of $Z$ case-by-case: it follows automatically from the fluid equations alone, via the
--   capacity bound (6.6) for $T$ and the algebraic relationships (6.1), (6.3), (6.4) for $Z, D, F$.
--
--   **Formalization note.** All four components' global Lipschitz continuity is asserted as one
--   conjunction, matching the book's single-sentence conclusion "any solution ... is globally
--   Lipschitz" (understood, as Definition 8.1 states, componentwise). The capacity consumption
--   matrix is nonnegative with no zero column (`hA`, `hAcol`) — the standing assumption on the SPN
--   data of Section 2.1 (binary $A$, no column entirely zero) — which is what makes the capacity
--   bound (6.6) control every component $\hat T_j$; without it an activity consuming no capacity
--   would have a $\hat T_j$ constrained only to be nondecreasing.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 136, Lemma 8.3

import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_LipschitzOn
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_FluidEquationData

namespace ProcessingNetworks.LyapunovCriteria

/-- Lemma 8.3, Dai & Harrison p. 136 (PDF p. 152): any solution `(D, F, T, Z)` of the fluid
equations (6.1)-(6.6) is globally Lipschitz (on `ℝ_+`, each component). -/
theorem fluid_model_solution_globally_lipschitz
    {I J K : ℕ} (dat : FluidEquationData I J K)
    (hA : ∀ k j, 0 ≤ dat.A k j) (hAcol : ∀ j, ∃ k, 0 < dat.A k j)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ)
    (hsol : IsFluidModelSolution dat Dh Fh Th Zh) :
    IsGloballyLipschitzOn Dh (Set.Ici (0 : ℝ)) ∧ IsGloballyLipschitzOn Fh (Set.Ici (0 : ℝ)) ∧
    IsGloballyLipschitzOn Th (Set.Ici (0 : ℝ)) ∧ IsGloballyLipschitzOn Zh (Set.Ici (0 : ℝ)) := by sorry

end ProcessingNetworks.LyapunovCriteria

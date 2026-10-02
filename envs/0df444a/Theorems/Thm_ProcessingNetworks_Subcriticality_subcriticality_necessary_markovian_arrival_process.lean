-- Prove2me | Theorems.Thm_ProcessingNetworks_Subcriticality_subcriticality_necessary_markovian_arrival_process
-- name    : ProcessingNetworks.Subcriticality.subcriticality_necessary_markovian_arrival_process
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:28:46.754559+00:00
-- url     : https://prove2.me/theorems/b5bbceee-a1a4-4605-a9a1-6f5b3dae84c1
-- title:
--   Corollary 5.4 — subcriticality is necessary under a Markovian arrival process
-- statement:
--   **Corollary 5.4.** Theorem 5.2 remains valid in the setting of Section 4.1, where Assumption 2.1
--   is weakened to allow a Markovian arrival process (MArP) in place of independent Poisson arrival
--   streams: if the (MArP-weakened) baseline stochastic assumptions and the Markov representation
--   hold and the SPN is stable, then its long-run arrival-rate vector $\lambda$ — now given by
--   Proposition E.7(a)'s SLLN for a MArP rather than by (2.14)'s Poisson-specific SLLN — still lies
--   in the subcritical region $\Lambda$.
--
--   The proof pattern is identical to Theorem 5.2's: the same sample-path decomposition of the
--   buffer-contents process, the same stationary-distribution expectation $x := \mathbb{E}_\pi[N(0)]$
--   (or $\mathbb{E}_\pi[\beta(0)]$ for the relaxed model), and the same conclusion $Rx = \lambda$,
--   $Ax < b$ — only the source of the arrival-rate SLLN changes.
--
--   **Formalization note.** The hypothesis structure `BaselineAssumptionsMArP` isolates exactly this
--   change: it agrees with `BaselineAssumptions` (Theorem 5.2's hypothesis) on parts (b)-(d) and
--   replaces part (a)'s Poisson-specific clause with the bare SLLN conclusion a MArP is assumed to
--   satisfy. The remaining hypotheses — the model data `dat`, the network processes obeying the basic
--   or relaxed model of Chapter 2 (with the service-rate vector a function of the ambient state in
--   the relaxed case), the Markov representation `M` in its augmented form (4.4), and stability —
--   and the conclusion are stated exactly as in `subcriticality_necessary_for_stability`.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 99, Corollary 5.4

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_Stability_Stable
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_Subcriticality_SPNPlanningData
import Definitions.Def_ProcessingNetworks_Subcriticality_StaticPlanningProblem
import Definitions.Def_ProcessingNetworks_Subcriticality_BaselineAssumptionsMArP

namespace ProcessingNetworks.Subcriticality

open MeasureTheory ProcessingNetworks.Stability

/-- Corollary 5.4 (Markovian arrival process), p. 99 (PDF p. 115): Theorem 5.2 remains valid when
Assumption 2.1 is weakened to allow a Markovian arrival process (`BaselineAssumptionsMArP`), with
`lam` now the I-vector of long-run arrival rates given by the MArP's own SLLN (Proposition E.7(a))
rather than by (2.14)'s Poisson-specific SLLN. The model hypotheses (basic or relaxed SPN on the
data `dat`, Markov representation in the augmented form (4.4), stability) are those of
`subcriticality_necessary_for_stability`. -/
theorem subcriticality_necessary_markovian_arrival_process
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {E : Fin I → ℝ → Ω → ℕ} {lam : Fin I → ℝ}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (ba : BaselineAssumptionsMArP I J E lam v φ m Γ Psi)
    (dat : SPNData I J K) {N0 : Fin J → ℕ} {Z0 : Fin I → ℕ}
    {S F N : ℝ → Ω → Fin J → ℕ} {T : ℝ → Ω → Fin J → ℝ} {D Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z)
    (hmodel : IsBasicSPN dat E v φ N0 Psi Z0 S F N T D Z ∨
      ∃ β : ℝ → Ω → Fin J → ℝ, IsRelaxedSPN dat E v φ N0 Psi Z0 S F N T D Z β ∧
        ∃ g : Xstate → Fin J → ℝ, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → β t ω = g (M.X t ω))
    (hstable : IsStable M) :
    lam ∈ SubcriticalRegion (SPNPlanningData.ofOutputMatrix dat.B Γ m
      (fun j => (ba.mean_service_time j).2.2) dat.A dat.b dat.b_pos) := by sorry

end ProcessingNetworks.Subcriticality

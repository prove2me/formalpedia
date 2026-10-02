-- Prove2me | Theorems.Thm_ProcessingNetworks_Subcriticality_subcriticality_necessary_for_stability
-- name    : ProcessingNetworks.Subcriticality.subcriticality_necessary_for_stability
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:30:36.940231+00:00
-- url     : https://prove2.me/theorems/cab4d641-ce52-47df-bcb2-7db5f5ca4170
-- title:
--   Theorem 5.2 — only subcritical networks can be stable (goal)
-- statement:
--   This is the book's own "only subcritical networks can be stable" theorem — the necessity half
--   of the central conjecture of Chapter 5, and the reason (per Section 5.4) that "throughout the
--   remainder of this book, attention is essentially restricted to subcritical networks."
--
--   **Theorem 5.2.** Consider either the basic SPN model (Section 2.3) or the relaxed model
--   (Section 2.4). If the baseline stochastic assumptions (Assumption 2.1) and the Markov
--   representation (Assumption 3.1) are satisfied, and the SPN is stable (Definition 3.6), then the
--   arrival-rate vector $\lambda$ must lie in the subcritical region
--   $$
--   \Lambda = \{\lambda \in \mathbb{R}_+^I : \gamma^\ast(\lambda) < 1\}
--   $$
--   of the static planning problem (Eq. 5.16).
--
--   The book's proof lets $\pi$ be the ambient chain's (unique, by stability) stationary
--   distribution, sets $x := \mathbb{E}_\pi[N(0)]$ (the stationary mean service-count vector), and
--   shows $Ax < b$ (from the sample-path capacity constraint $AN(t) \le b$ together with
--   $\Pr_\pi\{N(0) \ne 0\} < 1$) and $Rx = \lambda$ (via a strong law of large numbers for the
--   cumulative service-completion process, combined with the arrival and output SLLNs and
--   boundedness of the buffer-contents process under stability). Together these give $\lambda \in
--   \Lambda$ by the equivalent characterization (5.17) of the subcritical region.
--
--   **Formalization note.** The theorem is stated for the network model the book states it for.
--   `dat : SPNData` is the model data of Section 2.1 (binary $A$ and $B$ with no zero column,
--   capacities $b > 0$); the network processes $S, F, N, T, D, Z$ are required to obey either the
--   basic model of Section 2.3 (`IsBasicSPN`: full-speed service, $A N(t) \le b$, completions at
--   start time plus service time) or the relaxed model of Section 2.4 (`IsRelaxedSPN`: service rates
--   $\beta(t)$ with $A\beta \le b$, at most one open service per type, completion when cumulative
--   effort reaches the service size), in the latter case under a simply structured policy, recorded
--   as the service-rate vector being a function of the ambient state $X(t)$ (Remark 5.3: "for the
--   relaxed model that restriction is implicit"); both formulations include the system relations of
--   Section 2.5 — (2.7), (2.9), (2.10), (2.12), (2.31)–(2.34) and the key relationship (6.51) — that
--   the proof's sample-path representation (5.23) and the SLLN (5.24) for service completions rest
--   on. `Γ` and `m` are reused from `BaselineAssumptions` (Assumption 2.1(b)) via
--   `SPNPlanningData.ofOutputMatrix`, matching Eq. (5.3)'s own use of the same output-mean and
--   mean-service-time data, and stability is mission I's `IsStable` (positive recurrence of the
--   ambient continuous-time chain).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 96, Theorem 5.2

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_Stability_Stable
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_Subcriticality_SPNPlanningData
import Definitions.Def_ProcessingNetworks_Subcriticality_StaticPlanningProblem

namespace ProcessingNetworks.Subcriticality

open MeasureTheory ProcessingNetworks.Stability
open scoped NNReal

/-- Theorem 5.2 (only subcritical networks can be stable), p. 96 (PDF p. 112, crossing the page
break to PDF p. 113): consider either the basic SPN model of Section 2.3 (`IsBasicSPN`) or the
relaxed model of Section 2.4 under a simply structured policy (`IsRelaxedSPN`, with the service
rate vector `β(t)` a function of the ambient state `X(t)`, Remark 5.3), built on the model data
`dat` (Section 2.1) from the primitive stochastic elements `E, v, φ, Psi` and the initial data
`N0, Z0`. If the baseline stochastic assumptions (2.1) and the Markov representation (3.1) are
satisfied, and the SPN is stable, then its arrival-rate vector `lam` lies in the subcritical
region `Λ` (5.16) of the static planning problem with `R = (B - Γ)M⁻¹` (5.3), `A`, `b`. -/
theorem subcriticality_necessary_for_stability
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N0 : Fin J → ℕ} {E : Fin I → ℝ → Ω → ℕ} {lam : Fin I → ℝ≥0}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (ba : BaselineAssumptions I J N0 E lam v φ m Γ Psi)
    (dat : SPNData I J K) {Z0 : Fin I → ℕ}
    {S F N : ℝ → Ω → Fin J → ℕ} {T : ℝ → Ω → Fin J → ℝ} {D Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z)
    (hmodel : IsBasicSPN dat E v φ N0 Psi Z0 S F N T D Z ∨
      ∃ β : ℝ → Ω → Fin J → ℝ, IsRelaxedSPN dat E v φ N0 Psi Z0 S F N T D Z β ∧
        ∃ g : Xstate → Fin J → ℝ, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → β t ω = g (M.X t ω))
    (hstable : IsStable M) :
    (fun i => (lam i : ℝ)) ∈
      SubcriticalRegion (SPNPlanningData.ofOutputMatrix dat.B Γ m
        (fun j => (ba.mean_service_time j).2.2) dat.A dat.b dat.b_pos) := by sorry

end ProcessingNetworks.Subcriticality

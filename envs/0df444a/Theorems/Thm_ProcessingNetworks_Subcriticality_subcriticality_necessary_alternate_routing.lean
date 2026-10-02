-- Prove2me | Theorems.Thm_ProcessingNetworks_Subcriticality_subcriticality_necessary_alternate_routing
-- name    : ProcessingNetworks.Subcriticality.subcriticality_necessary_alternate_routing
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:29:12.111239+00:00
-- url     : https://prove2.me/theorems/5d674771-f355-4dd4-8f5c-caf788fdc17e
-- title:
--   Corollary 5.5 — subcriticality is necessary under alternate routing with immediate commitment
-- statement:
--   **Corollary 5.5.** Consider an SPN with alternate routing and immediate commitment (Section
--   4.2), maintaining that section's assumptions: uncommitted arrivals from $L$ sources at rates
--   $\nu_\ell$, routable per a zero-one source-buffer matrix $G$. If the network is stable, then it
--   must be subcritical as defined by the augmented static planning problem (5.12)-(5.15): the
--   optimal objective value satisfies $\gamma^\ast < 1$.
--
--   The book's proof combines two already-established facts: Proposition 4.1 supplies a routing
--   matrix $\varphi$ and arrival-rate vector $\lambda$ realizing the SLLN limits and the balance
--   identities (5.10)-(5.11), and the argument of Theorem 5.2 (applied to the resulting $\lambda$)
--   supplies an activity-rate vector $x$ with $Rx = \lambda$ and $Ax < b$ — together giving
--   feasibility of the augmented SPP at $\gamma < 1$.
--
--   **Formalization note.** The hypotheses are those of Proposition 4.1 (the augmented model of
--   Section 4.2: uncommitted arrivals `U` with the SLLN (4.5) at rates `nu > 0`, the routing process
--   `V` with (4.6), class-level arrivals `E` given by (4.7), the routing increments read off the
--   ambient chain's transitions, bounded exit rates) together with those of Theorem 5.2 (the
--   processing-variable assumptions 2.1(b)–(d), the network processes obeying the basic or relaxed
--   model of Chapter 2 on the model data `dat` with the class-level arrivals `E`, the Markov
--   representation, stability); the conclusion is the corollary's own (augmented subcriticality,
--   `IsAugmentedSubcritical`), exactly as the book's proof combines Proposition 4.1 with the argument
--   of Theorem 5.2.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 99, Corollary 5.5

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_Stability_Stable
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_Subcriticality_SPNPlanningData
import Definitions.Def_ProcessingNetworks_Subcriticality_StaticPlanningProblem
import Definitions.Def_ProcessingNetworks_Subcriticality_BaselineAssumptionsMArP

namespace ProcessingNetworks.Subcriticality

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability

/-- Corollary 5.5 (alternate routing with immediate commitment), p. 99 (PDF p. 115): consider an
SPN with alternate routing and immediate commitment, maintaining the assumptions of Section 4.2 —
uncommitted arrivals `U` from `L` sources with the SLLN (4.5) and strictly positive rates `nu`,
zero-one source-buffer matrix `G`, routing process `V` with (4.6), class-level arrivals `E` given
by (4.7), the routing increments read off the ambient chain's transitions (4.8), bounded exit rates
(D.8), the processing-variable assumptions 2.1(b)–(d), and the network processes obeying the basic
or relaxed model on the data `dat` (with `β` a function of the ambient state in the relaxed
case). If the network is stable, then it is subcritical in the sense of the augmented static
planning problem (5.12)–(5.15): its optimal objective value satisfies `γ* < 1`. -/
theorem subcriticality_necessary_alternate_routing
    {Ω : Type*} [MeasureSpace Ω] {L I J K : ℕ} {Xstate : Type*} [Countable Xstate]
    {N0 : Fin J → ℕ} {E : Fin I → ℝ → Ω → ℕ}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (pa : ProcessingVariableAssumptions I J E v φ m Γ Psi)
    (G : Matrix (Fin L) (Fin I) ℝ) (hG : ∀ ℓ i, G ℓ i = 0 ∨ G ℓ i = 1)
    (U : Fin L → ℝ → Ω → ℕ) (nu : Fin L → ℝ) (hnu : ∀ ℓ, 0 < nu ℓ)
    (hU : ℙ {ω | Filter.Tendsto (fun t : ℝ => fun ℓ => (U ℓ t ω : ℝ) / t)
        Filter.atTop (nhds nu)} = 1)
    (V : Fin L → Fin I → ℝ → Ω → ℕ)
    (hVG : ∀ ℓ i, G ℓ i = 0 → ∀ (t : ℝ) (ω : Ω), V ℓ i t ω = 0)
    (hVsum : ∀ (ℓ : Fin L) (t : ℝ) (ω : Ω), ∑ i, V ℓ i t ω = U ℓ t ω)
    (hE : ∀ (i : Fin I) (t : ℝ) (ω : Ω), E i t ω = ∑ ℓ, V ℓ i t ω)
    (dat : SPNData I J K) {Z0 : Fin I → ℕ}
    {S F N : ℝ → Ω → Fin J → ℕ} {T : ℝ → Ω → Fin J → ℝ} {D Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z) (hrate : ∃ C : ℝ, ∀ x, M.rate x ≤ C)
    (hVjump : ∃ g : Xstate → Xstate → Fin L → Fin I → ℕ,
      IsJumpFunctional M (fun t ω => fun ℓ i => V ℓ i t ω) g)
    (hmodel : IsBasicSPN dat E v φ N0 Psi Z0 S F N T D Z ∨
      ∃ β : ℝ → Ω → Fin J → ℝ, IsRelaxedSPN dat E v φ N0 Psi Z0 S F N T D Z β ∧
        ∃ g : Xstate → Fin J → ℝ, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → β t ω = g (M.X t ω))
    (hstable : IsStable M) :
    IsAugmentedSubcritical (SPNPlanningData.ofOutputMatrix dat.B Γ m
      (fun j => (pa.mean_service_time j).2.2) dat.A dat.b dat.b_pos) G nu := by sorry

end ProcessingNetworks.Subcriticality

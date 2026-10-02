-- Prove2me | Theorems.Thm_ProcessingNetworks_TaskAllocation_fluid_limit_stability_implies_model_stability
-- name    : ProcessingNetworks.TaskAllocation.fluid_limit_stability_implies_model_stability
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:42:59.711419+00:00
-- url     : https://prove2.me/theorems/d75df0da-a81f-4411-98fc-444a4b300a69
-- title:
--   Theorem 11.5 — fluid limit stability implies model stability (milestone)
-- statement:
--   **Theorem 11.5.** Consider a task allocation model satisfying all the assumptions enunciated
--   above, operating under a simply structured routing policy. If its associated fluid limit is
--   stable, then the task allocation model itself is stable (i.e. the ambient Markov chain $X$
--   described in Section 11.4 is positive recurrent).
--
--   This is the chapter's own replacement for Theorem 6.2 (mission III), needed because the task
--   allocation model violates two of Theorem 6.2's standing hypotheses: Poisson (not MArP) arrivals,
--   and no immediate-commitment routing.
--
--   **Formalization note.** The model is the standard setup `TaskAllocationProcessFamily` on the
--   ambient chain `Mrep` (mission I's `MarkovRepresentation` for the flat class index, with
--   $Z^x(t) \sim Z(t) \mid X(0) = x$ built into the setup, which is the link the proof's use of
--   Lemma 3.7 needs), under "all the assumptions enunciated above": the SLLN of the Markovian
--   arrival process (Proposition E.7, `hU`) and, per Remark 11.1, i.i.d. positive service times
--   with finite mean $m_{\ell k}$ for every class (`hv`, `hvpos`, `hm`). The conclusion is positive
--   recurrence of the continuous-time ambient chain (Definition D.15, mission I's
--   `PositiveRecurrent`), not of an unrelated jump kernel.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 219, Theorem 11.5

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_TaskAllocation_TaskAllocationModel
import Definitions.Def_ProcessingNetworks_TaskAllocation_AmbientChain
import Definitions.Def_ProcessingNetworks_TaskAllocation_ProcessFamily

namespace ProcessingNetworks.TaskAllocation

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability

/-- Theorem 11.5, Dai & Harrison p. 219 (PDF p. 235): consider a task allocation model satisfying
all the assumptions enunciated above — the standard setup `fam` on the ambient chain `Mrep`
(Section 11.4), the Markovian arrival process `U` with its SLLN (Proposition E.7, `hU`), and for
every class an i.i.d. sequence of positive service times with finite mean `m ℓ k` (Remark 11.1,
`hv`, `hm`) — operating under a simply structured routing policy. If its associated fluid limit is
stable (`TaskAllocationFluidLimitStable`, Definition 6.1 restated), then the task allocation
model itself is stable, i.e. the ambient Markov chain `X` described in Section 11.4 is positive
recurrent (Definition D.15, mission I's `PositiveRecurrent`). -/
theorem fluid_limit_stability_implies_model_stability
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {L K : ℕ}
    (dat : TaskAllocationData L K)
    {N : ℝ → Ω → Fin (L * K) → ℕ} {Z : ℝ → Ω → Fin (L * K) → ℕ}
    {Mrep : MarkovRepresentation Xstate (L * K) (L * K) N Z}
    {U : Fin L → ℝ → Ω → ℕ} {v : Fin L → Fin K → ℕ → Ω → ℝ}
    (fam : TaskAllocationProcessFamily dat Mrep U v)
    (hU : ℙ {ω | ∀ ℓ, Tendsto (fun t : ℝ => (U ℓ t ω : ℝ) / t) atTop (nhds (dat.nu ℓ))} = 1)
    (hv : ∀ ℓ k, iIndepFun (fun n : ℕ => v ℓ k n) ℙ ∧
      ∀ n, IdentDistrib (v ℓ k n) (v ℓ k 0) ℙ ℙ)
    (hvpos : ∀ ℓ k n ω, 0 < v ℓ k n ω)
    (hm : ∀ ℓ k, Integrable (v ℓ k 0) ℙ ∧ ∫ ω, v ℓ k 0 ω ∂ℙ = dat.m ℓ k)
    (hFluidLimitStable : TaskAllocationFluidLimitStable fam) :
    PositiveRecurrent Mrep.jump Mrep.rate := by sorry

end ProcessingNetworks.TaskAllocation

-- Prove2me | Theorems.Thm_ProcessingNetworks_PacketNetworks_rps_load_condition_implies_stability
-- name    : ProcessingNetworks.PacketNetworks.rps_load_condition_implies_stability
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T20:05:26.402119+00:00
-- url     : https://prove2.me/theorems/3eb824e0-48ba-4314-af14-bf69e9e69297
-- title:
--   Theorem 12.28 — the load condition implies RPS fluid stability and positive recurrence (goal)
-- statement:
--   This is the goal theorem of the mission, and the book's own final capstone.
--
--   **Theorem 12.28.** Assume that the load condition (12.50) is satisfied: $\rho < \hat c$ for
--   some $\hat c \in \langle C\rangle$, where $\rho := A\alpha$ (Eq. 12.49) and $\alpha := R^{-1}
--   \lambda$ (Eq. 12.48). Then (a) the RPS fluid model is stable, and hence (b) the DTMC $Z$ under
--   the RPS control policy is positive recurrent.
--
--   The book's own proof: (a) follows from Proposition 12.26 (the RPS fluid model is a special
--   case of the PF fluid model) together with Theorem 10.5 (mission IX), since the load condition
--   (12.50) specializes the general PF load condition (10.37) exactly (both use $m\equiv 1$); (b)
--   follows from (a) and Theorem 12.27.
--
--   **Formalization note.** $\alpha$ is characterized by the fixed point $\alpha = \lambda +
--   P'\alpha$ (mission IX's `IsTotalArrivalRates`, imported), $\rho<\hat c$ by
--   `groupAggregate`/`hullFinset`. The chain and the standing assumptions are as in Theorem
--   12.27, positive recurrence on $\mathcal X$ likewise. The hypothesis `hdom` records that
--   $\langle C\rangle$ qualifies as the domain $\tilde{\mathcal A}$ of Section 10.1 (bounded,
--   closed, convex, monotone, nontrivial), the standing assumption of Theorem 10.5 through which
--   the book proves (a); it holds when $C$ is taken closed under decreasing a configuration, which
--   changes neither $S$ nor the scheduler.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 255 (PDF p. 271), Theorem 12.28, Eqs. (12.48)-(12.50)

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSFluidModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_BPAmbientChain

namespace ProcessingNetworks.PacketNetworks

open MeasureTheory ProbabilityTheory

/-- Theorem 12.28, Dai & Harrison p. 255 (PDF p. 271) — the goal theorem of this mission. In a
fixed-routing packet network under the chapter's standing assumptions (Assumptions 12.1 and 12.4,
`S` from (12.10), primitives satisfying Section 12.1's stochastic assumptions with arrival rate
vector `λ`), operated under the random proportional scheduler with `jump` the one-step kernel of
the DTMC `Z` it generates, assume the load condition (12.50): `ρ < ĉ` for some `ĉ ∈ ⟨C⟩`, where
`ρ = Aα` (12.49) and `α = R⁻¹λ`, i.e. `α = λ + P'α` (12.48). Then (a) the RPS fluid model is stable,
and hence (b) the DTMC `Z` is positive recurrent (on its state space `𝒳` of states reachable from
`0`). `hdom` records that `⟨C⟩` qualifies as the domain `Ã` of the PF fluid model of Section 10.4
(bounded, closed, convex, monotone, nontrivial), the standing assumption of Theorem 10.5 through
which the book proves (a); it holds when `C` is taken closed under decreasing a configuration. -/
theorem rps_load_condition_implies_stability
    {I K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (fr : FixedRoutingData I K) (h121 : SatisfiesAssumption121 fr.dat)
    (h124 : SatisfiesAssumption124 fr.cfg)
    (hdom : ProportionalFairness.IsPFDomain (hullFinset fr.cfg.C))
    (S : Finset (Fin I → ℕ)) (hS : IsScheduleSet fr.cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I I Ω) (hP : PrimitiveAssumptions P lam)
    (hRPS : IsRPSPolicy fr S P.f)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain fr.dat P jump)
    (alpha : Fin I → ℝ) (halpha : ProportionalFairness.IsTotalArrivalRates (toPFData fr lam) alpha)
    (hload : ∃ chat ∈ hullFinset fr.cfg.C,
      ∀ k, ProportionalFairness.groupAggregate fr.linkDesig alpha k < chat k) :
    RPSFluidStable fr S lam ∧ PositiveRecurrentOn jump (reachableFrom jump 0) := by sorry

end ProcessingNetworks.PacketNetworks

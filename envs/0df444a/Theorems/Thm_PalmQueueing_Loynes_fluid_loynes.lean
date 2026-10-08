-- Prove2me | Theorems.Thm_PalmQueueing_Loynes_fluid_loynes
-- name    : PalmQueueing.Loynes.fluid_loynes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T23:47:17.60763+00:00
-- url     : https://prove2.me/theorems/56144c5f-d920-4d23-b3f4-fe085180587b
-- title:
--   Theorem 2.7.1 — the Loynes theorem for fluid queues
-- statement:
--   **Theorem 2.7.1.** If $\lambda < \mu$, then there exists a **minimal** finite
--   $\theta_t$-compatible workload process satisfying (2.7.6), defined by
--   $$ W(t) = W(0)\circ\theta_t = \sup_{u \le t} \big(A_{u,t} - C_{u,t}\big) . \tag{2.7.7} $$
--
--   This is Loynes' theorem with the discrete customers of §2.1 replaced by two $\theta_t$-compatible
--   non-negative random measures on the line, $A_{s,t}$ the fluid arriving on $[s,t)$ and $C_{s,t}$
--   the most the server can drain there, with positive finite intensities $\lambda$ and $\mu$.
--
--   Two differences from Theorem 2.1.1 are the book's and are kept. The construction gives the
--   **minimal** solution, not the unique one: §2.7 makes no uniqueness claim. And the stability
--   condition is $\lambda < \mu$ on the two intensities rather than $\rho < 1$, which is the same
--   condition when the service measure is deterministic at unit rate,
--   $C_{s,t} = c\cdot(t-s)$.
--
--   The a.s. finiteness of $W(0)$ follows from the pointwise ergodic theorem, which together with
--   $\lambda < \mu$ implies $\lim_{u\to-\infty}(A_{u,0} - C_{u,0}) = -\infty$ $P$-a.s.; the
--   $\theta_t$-compatibility of (2.7.7) is immediate from that of $A$ and $C$; and (2.7.6) follows
--   from splitting the supremum at $s$. Boundedness above of the supremum set is therefore part of
--   the conclusion, not a hypothesis.
--
--   **Formalization Note.** The finiteness and formula (2.7.7), and the recurrence (2.7.6), hold $P$-almost surely, as the book's proof says ("the a.s. finiteness of $W(0)$"). Minimality is: every $\theta_t$-compatible process satisfying (2.7.6) $P$-a.s. dominates $W$ $P$-a.s. The intensities $\lambda = E[A_{0,1}]$ and $\mu = E[C_{0,1}]$ are finite ($A_{0,1}$, $C_{0,1}$ integrable) and positive.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 131, Theorem 2.7.1

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Loynes_SingleServerQueue
import Definitions.Def_PalmQueueing_Loynes_FluidQueue
import Definitions.Def_PalmQueueing_Loynes_StationaryRegime

/-!
# Theorem 2.7.1: the Loynes theorem for fluid queues (§2.7.2, p.131)
-/

namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 2.7.1** (§2.7.2, p.131). If `λ < µ`, then there exists a **minimal** finite
`θ_t`-compatible workload process satisfying `(2.7.6)`, defined by

`(2.7.7)  W(t) = W(0) ∘ θ_t = sup_{u ≤ t} ( A_{u,t} − C_{u,t} )`.

This is Loynes' theorem with the discrete customers of §2.1 replaced by two `θ_t`-compatible
non-negative random measures on the line: `A_{s,t}` is the fluid arriving on `[s,t)` and `C_{s,t}`
the most the server can drain there, with positive finite intensities `λ` and `µ`.

Two differences from Theorem 2.1.1 are the book's and are kept. The construction gives the
**minimal** solution, not the unique one — §2.7 makes no uniqueness claim. And the stability
condition is `λ < µ` on the two intensities rather than `ρ < 1`, which is the same condition when
the service measure is deterministic at unit rate.

`BddAbove` on the supremum set is part of the conclusion, which is what "finite" means here: the
book's proof gets it from the pointwise ergodic theorem, via
`lim_{u→−∞} (A_{u,0} − C_{u,0}) = −∞` `P`-a.s. Without it the `sSup` of an unbounded set would
default to `0` and the zero process would satisfy the identity.

The finiteness and the recurrence `(2.7.6)` hold `P`-a.s., as the proof says ("the a.s. finiteness
of `W(0)`"): on a `P`-null `θ_t`-invariant set of sample paths where `A` outgrows `C` no finite
solution exists, so a claim for every `ω` would be false. Minimality is among the compatible
processes satisfying `(2.7.6)` `P`-a.s. -/
theorem fluid_loynes (θ : Flow Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (herg : IsErgodicFlow θ P)
    (A C : ℝ → ℝ → Ω → ℝ) (hA : IsFlowMeasure θ A) (hC : IsFlowMeasure θ C)
    (lam mu : ℝ)
    (hAint : Integrable (A 0 1) P) (hCint : Integrable (C 0 1) P)
    (hlam : 0 < lam ∧ lam = ∫ ω, A 0 1 ω ∂P)
    (hmu : 0 < mu ∧ mu = ∫ ω, C 0 1 ω ∂P)
    (hstab : lam < mu) :
    ∃ W : ℝ → Ω → ℝ,
      IsCompatible θ W ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ,
        BddAbove (fluidLoynesSet A C t ω) ∧ W t ω = sSup (fluidLoynesSet A C t ω)) ∧
      (∀ᵐ ω ∂P, IsFluidWorkloadPath A C W ω) ∧
      (∀ W' : ℝ → Ω → ℝ, IsCompatible θ W' → (∀ᵐ ω ∂P, IsFluidWorkloadPath A C W' ω) →
        ∀ᵐ ω ∂P, ∀ t : ℝ, W t ω ≤ W' t ω) := by sorry

end PalmQueueing.Loynes

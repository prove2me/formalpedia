-- Prove2me | Theorems.Thm_ProcessingNetworks_EntropyIneq_Supplement_theorem_D_24
-- name    : ProcessingNetworks.EntropyIneq.Supplement.theorem_D_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:14:26.440019+00:00
-- url     : https://prove2.me/theorems/e9b2915c-22f2-551a-a63a-00ce0ac0feb3
-- title:
--   Theorem D.24 — convergence to equilibrium or zero statewise mass
-- statement:
--   Let $X$ be an irreducible regular continuous-time Markov chain on a nonempty countable state space, with an arbitrary initial distribution $\rho$.
--
--   1. If $X$ is positive recurrent, then it has a unique stationary distribution $\pi$, every $\pi(j)$ is strictly positive, and
--      $$
--      \lim_{t\to\infty}\mathbb P_\rho\{X(t)=j\}=\pi(j)>0\qquad(j\in S).
--      $$
--   2. If $X$ is not positive recurrent, then
--      $$
--      \lim_{t\to\infty}\mathbb P_\rho\{X(t)=j\}=0\qquad(j\in S).
--      $$
--
--   The second case covers both null-recurrent and transient chains.
--
--   This is the appendix's statewise convergence-to-equilibrium dichotomy.
--
--   **Formalization Note** The time-$t$ law is the initial PMF bound through the transition semigroup. Limits run over nonnegative real time. Existence, stationarity, uniqueness and strict positivity of $\pi$ are all explicit in the first clause.
--
--   Differences from the source:
--   - encoding: probabilities P{X(t)=j} from an arbitrary initial distribution ρ → coordinates of the initial PMF bound through the transition semigroup; reason: this is the law-level representation of the same regular CTMC and preserves every initial distribution
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Theorem D.24, p.295 (PDF 311), proof continuing p.296 (PDF 312)

import Mathlib
import Definitions.Def_ProcessingNetworks_EntropyIneq_Supplement_RegularCTMC
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

namespace ProcessingNetworks.EntropyIneq.Supplement

open MatrixAnalytic.ProductForm Filter Topology
open scoped NNReal

/-- **Theorem D.24.** For an irreducible regular CTMC with arbitrary initial distribution, the
one-time mass of every fixed state converges to the positive mass of the unique stationary
distribution in the positive-recurrent case, and converges to zero otherwise.

Dai & Harrison, *Processing Networks* (pre-publication draft 2020-4-2, spnbook.org),
Theorem D.24, p.295 (PDF 311), with the proof continuing on p.296 (PDF 312).

**Formalization Note** `M.initial.bind (M.transition t)` is the law of `X(t)` from the arbitrary
initial distribution stored in `M`. The two implications retain both cases of the theorem. In the
positive-recurrent case the conclusion includes stationarity, uniqueness, strict positivity at
every state, and convergence; the non-positive-recurrent case includes both null recurrence and
transience. Limits are taken along nonnegative real time. -/
theorem theorem_D_24 {S : Type*} [Countable S] [DecidableEq S]
    (M : RegularCTMC S)
    (hirr : ProcessingNetworks.Stability.Irreducible
      (ProcessingNetworks.CTMCFoster.jumpPMF M.isGenerator)) :
    (ProcessingNetworks.Stability.PositiveRecurrent
        (ProcessingNetworks.CTMCFoster.jumpPMF M.isGenerator) (holdRate M.generator) →
      ∃ pi : PMF S,
        ProcessingNetworks.Stability.IsStationaryDistribution
          (ProcessingNetworks.CTMCFoster.jumpPMF M.isGenerator) (holdRate M.generator) pi ∧
        (∀ pi' : PMF S, ProcessingNetworks.Stability.IsStationaryDistribution
          (ProcessingNetworks.CTMCFoster.jumpPMF M.isGenerator) (holdRate M.generator) pi' →
          pi' = pi) ∧
        ∀ j : S, 0 < pi j ∧
          Tendsto (fun t : ℝ≥0 => (M.initial.bind (M.transition t) j).toReal)
            atTop (nhds (pi j).toReal)) ∧
      (¬ ProcessingNetworks.Stability.PositiveRecurrent
          (ProcessingNetworks.CTMCFoster.jumpPMF M.isGenerator) (holdRate M.generator) →
        ∀ j : S, Tendsto (fun t : ℝ≥0 => (M.initial.bind (M.transition t) j).toReal)
          atTop (nhds 0)) := by sorry

end ProcessingNetworks.EntropyIneq.Supplement

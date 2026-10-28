-- Prove2me | Theorems.Thm_UniformCounting_uniformProbability_mono
-- name    : UniformCounting.uniformProbability_mono
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T15:18:33.924037+00:00
-- url     : https://prove2.me/theorems/46a2f1a3-8075-442b-b90b-5e26c619f98d
-- title:
--   The uniform counting probability is monotone in the event
-- statement:
--   Let $\Omega$ be a finite type and let
--
--   $$
--   \mathbb{P}(P) \;=\; \frac{\#\{\omega \in \Omega : P(\omega)\}}{\#\Omega}
--   $$
--
--   be the uniform counting probability of an event $P$. If $P$ implies $Q$ pointwise, then
--
--   $$
--   \mathbb{P}(P) \;\le\; \mathbb{P}(Q).
--   $$
--
--   This is the most basic property one needs of a uniform probability, and it is what lets a
--   high-probability guarantee be weakened: having bounded $\mathbb{P}$ of a strong event from
--   below, one concludes the same bound for any consequence of it. In the analysis of an online
--   algorithm run on a uniformly random arrival sequence, the strong event is typically a
--   conjunction of per-step bounds and the weak one is the guarantee actually claimed.
--
--   **Formalization Note** No nonemptiness hypothesis is needed: when $\#\Omega = 0$ both sides are
--   $0/0 = 0$ in Lean's convention, and the inequality holds. The event is an arbitrary
--   `Prop`-valued predicate, with decidability supplied classically, exactly as the platform's
--   `uniformProbability` does.
-- source:
--   Used throughout the high-probability analysis in Feldman, Mehta, Mirrokni & Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, Proc. 50th IEEE FOCS (2009) 117-126, DOI 10.1109/FOCS.2009.72, proof of Theorem 4; stated here for the uniform counting probability on an arbitrary finite sample space.

import Mathlib
import Definitions.Def_OnlineStochMatching_SuggestedMatching_BallsInBins

namespace UniformCounting

/-- The uniform counting probability on a finite sample space is monotone in the event. -/
theorem uniformProbability_mono {Ω : Type} [Fintype Ω] (P Q : Ω → Prop)
    (h : ∀ ω, P ω → Q ω) :
    OnlineStochMatching.SuggestedMatching.uniformProbability P ≤
      OnlineStochMatching.SuggestedMatching.uniformProbability Q := by sorry

end UniformCounting

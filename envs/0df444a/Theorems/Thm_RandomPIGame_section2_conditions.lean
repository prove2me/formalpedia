-- Prove2me | Theorems.Thm_RandomPIGame_section2_conditions
-- name    : RandomPIGame.section2_conditions
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:04.796857+00:00
-- url     : https://prove2.me/theorems/60596252-0b4b-4bd4-8afc-5305f900778d
-- title:
--   §2, p.8: $\mathbb P_p$ is the unique Borel probability measure satisfying [1]–[2]
-- statement:
--   Let $p$ be a primitive distribution. The measure $\mathbb P_p$ on $\Omega$ satisfies the following two conditions, and it is the only Borel probability measure on $\Omega$ that does.
--
--   1. The random variable $(\iota(\oslash),\gamma(\oslash),\xi(\oslash))$ is distributed according to $p$.
--   2. For each $(i,k,n)\in S$ with $n\in\mathbb N_+$, if $p_i(k,n)>0$, then the random variables $\omega(1),\dots,\omega(n)$ are independent under the conditional measure $\mathbb P(\cdot\mid E(i,k,n))$, and each is distributed according to $\mathbb P$.
--
--   This is the form of the recursive structure of $\mathbb P_p$ used to analyse the value by conditioning on the root.
--
--   Differences from the source:
--   - encoding: indices j, ℓ ∈ {1, …, n} → an index j : Fin n standing for j + 1; reason: a reindexing; no instance changes
--   - encoding: ω(j) is defined on {ξ_ω(⊘) ≥ j} → Game.child is total and returns ω when (j) is not a node; reason: every use restricts to E(i, k, n) with j ≤ n or conditions on that event, so the default never matters
--   - encoding: capacities and thresholds k in [0, ∞) → capacities and thresholds k in ℝ≥0; reason: Lean convention; the same numbers
--   - encoding: P_p is the Borel measure on Ω characterized by (2.4)–(2.5) → gameMeasure p is the pushforward of Measure.infinitePi under g; reason: this is the paper's own construction on p.8; the milestone section2_measure proves g measurable and identifies the two
--   - encoding: probabilities P(·) → Measure.real, a real number; reason: all measures involved are finite, so nothing is lost
-- source:
--   Flesch, Predtetchinski & Suomala, Random perfect information games, arXiv:2104.10528v1, §2, p.8, [1]–[2]

import Mathlib
import Definitions.Def_RandomPIGame_Primitive
import Definitions.Def_RandomPIGame_Game
import Definitions.Def_RandomPIGame_Measure

open MeasureTheory

namespace RandomPIGame

/-- `P_p` satisfies the conditions [1] and [2], and it is the unique Borel probability measure on
`Ω` that does. arXiv:2104.10528v1, §2, p.8, [1]–[2]. -/
theorem section2_conditions (p : Measure S) [IsProbabilityMeasure p] :
    SatisfiesConditions p (gameMeasure p) ∧
      ∀ Q : Measure Game, IsProbabilityMeasure Q → SatisfiesConditions p Q → Q = gameMeasure p := by sorry

end RandomPIGame

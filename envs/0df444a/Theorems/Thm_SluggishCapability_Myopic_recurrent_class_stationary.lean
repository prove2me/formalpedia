-- Prove2me | Theorems.Thm_SluggishCapability_Myopic_recurrent_class_stationary
-- name    : SluggishCapability.Myopic.recurrent_class_stationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:34.409089+00:00
-- url     : https://prove2.me/theorems/e82090c1-a2b5-4bf3-acd1-92c470c4a900
-- title:
--   Proof of Proposition 1, p. 17 — each recurrent class of a finite chain carries an invariant distribution
-- statement:
--   Let $K$ be a stochastic matrix on a finite set $X$ and let $x \in X$ be recurrent (every state reachable from $x$ reaches $x$ back). Then there is an invariant distribution $\nu$ of $K$ with
--   $$\nu(x) > 0 \quad\text{and}\quad \nu(y) > 0 \implies y \text{ is reachable from } x .$$
--
--   The paper identifies the long-run frequencies of the pairs visited on a sample path with the invariant distribution of the recurrent class the path settles in. This lemma supplies that distribution for every recurrent class, so that statements proved for invariant distributions apply to every class.
-- source:
--   Eliaz, Spiegler, Capability Building in Sluggish Organizations, authors' manuscript of March 28, 2022 (Management Science 2023, doi:10.1287/mnsc.2022.4445), p. 17, proof of Proposition 1 (recurrent pairs and their invariant distribution)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting

open MarkovMixing

namespace SluggishCapability.Myopic

/-- Proof of Proposition 1, p. 17: every recurrent state `x` of a finite Markov chain `K` carries
an invariant distribution `ν` that charges `x` and is supported in the recurrent class of `x`
(every state it charges is reachable from `x`). -/
theorem recurrent_class_stationary {X : Type*} [Fintype X] [DecidableEq X]
    (K : Matrix X X ℝ) (hK : IsStochastic K) (x : X) (hx : IsRecurrentState K x) :
    ∃ ν : X → ℝ, IsStationary K ν ∧ 0 < ν x ∧ ∀ y, 0 < ν y → Reaches K x y := by sorry

end SluggishCapability.Myopic

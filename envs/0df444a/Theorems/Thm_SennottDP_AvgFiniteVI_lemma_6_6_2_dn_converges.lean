-- Prove2me | Theorems.Thm_SennottDP_AvgFiniteVI_lemma_6_6_2_dn_converges
-- name    : SennottDP.AvgFiniteVI.lemma_6_6_2_dn_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T09:31:49.56755+00:00
-- url     : https://prove2.me/theorems/77ba09b7-1351-4a89-8bde-3f7fe605caff
-- title:
--   Lemma 6.6.2 — d_n converges to a constant on an aperiodic recurrent class of an optimal policy
-- statement:
--   Let $\Delta$ be an MDC with finite state space $S$ whose minimum average cost is a constant $J$, and let $d_n(i) = h(i) + nJ - v_n(i)$ as in Theorem 6.4.2(iv), for a distinguished state $z$. Let $e$ be an average cost optimal stationary policy whose induced chain has an aperiodic positive recurrent class $R$. Then there is a finite constant $D$ with
--   $$\lim_{n\to\infty} d_n(i) = D, \qquad i \in R.$$
--
--   This is the step at which aperiodicity enters value iteration.
--
--   **Formalization Note** $R$ is given as the communicating class of a positive recurrent state $x$ of the chain induced by $e$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 115–116, Lemma 6.6.2

import Mathlib
import Definitions.Def_SennottDP_AvgFiniteVI_ACOE

namespace SennottDP.AvgFiniteVI

open scoped ENNReal NNReal Topology
open Filter

/-- Lemma 6.6.2 (Sennott, pp. 115–116). Let `S` be finite, assume that the minimum average cost
is a constant `J`, and let `d_n(i) = h(i) + nJ − v_n(i)` be as in Theorem 6.4.2(iv) (for a
distinguished state `z`). Let `e` be an average cost optimal stationary policy inducing a Markov
chain with an aperiodic positive recurrent class `R` (the communicating class of the positive
recurrent state `x`). Then there is a finite constant `D` with `lim_{n→∞} d_n(i) = D` for
`i ∈ R`. -/
theorem lemma_6_6_2_dn_converges {S : Type*} {Act : Type*} [Fintype S]
    (M : MDC S Act) (J : ℝ≥0) (hJ : ∀ i : S, avgValue M i = J) (z : S)
    (e : StationaryPolicy M) (he : IsAverageOptimal e.toPolicy) (x : S)
    (hx : SennottDP.AvgFinite.PositiveRecurrent (inducedChain M e) x)
    (hR : IsAperiodicClass (inducedChain M e) (SennottDP.AvgFinite.commClass (inducedChain M e) x)) :
    ∃ D : ℝ, ∀ i ∈ SennottDP.AvgFinite.commClass (inducedChain M e) x,
      Tendsto (fun n : ℕ => dSeq M z J n i) atTop (𝓝 D) := by sorry

end SennottDP.AvgFiniteVI

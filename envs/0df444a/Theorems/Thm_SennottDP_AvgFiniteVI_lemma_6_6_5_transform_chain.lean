-- Prove2me | Theorems.Thm_SennottDP_AvgFiniteVI_lemma_6_6_5_transform_chain
-- name    : SennottDP.AvgFiniteVI.lemma_6_6_5_transform_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T09:32:21.28686+00:00
-- url     : https://prove2.me/theorems/75ad0643-6c20-4604-adb1-1126ed01c81b
-- title:
--   Lemma 6.6.5 — the aperiodicity transformation preserves classes and steady states and makes classes aperiodic
-- statement:
--   Let $\Delta$ be an MDC with finite state space $S$, $0 < \tau < 1$, and $\Delta^*$ the transformed MDC of (6.64). Fix a stationary policy $e$ and let MC, MC* be the Markov chains it induces in $\Delta$ and $\Delta^*$. Then:
--
--   1. the communicating classes of MC and MC* are identical, and hence so are the positive recurrent classes;
--   2. every positive recurrent class of MC* is aperiodic;
--   3. for a positive recurrent class $R$, $\pi^*_j = \pi_j$ for $j \in R$, and
--   $$J^*_R = \tau J_R,$$
--   where $J_R$ and $J^*_R$ are the average costs of $e$ on $R$ in $\Delta$ and $\Delta^*$.
--
--   **Formalization Note** Part 3 is stated at every state $j$ of the class $R$ (the average cost of a stationary policy is constant on a positive recurrent class).
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 121, Lemma 6.6.5

import Mathlib
import Definitions.Def_SennottDP_AvgFiniteVI_ACOE
import Definitions.Def_SennottDP_AvgFiniteVI_Transform

namespace SennottDP.AvgFiniteVI

open scoped ENNReal NNReal

/-- Lemma 6.6.5 (Sennott, p. 121). Let `S` be finite, `0 < τ < 1`, and let `Δ*` be the
aperiodicity transformation (6.64) of `Δ`. For a fixed stationary policy `e`, with `MC` and `MC*`
the Markov chains it induces in `Δ` and `Δ*`:
(i) the communicating classes of `MC` and `MC*` are identical, and hence the positive recurrent
classes are identical;
(ii) every positive recurrent class of `MC*` is aperiodic;
(iii) for a positive recurrent class `R`, `π*_j = π_j` for `j ∈ R`, and `J*_R = τ J_R` (the
average cost of `e` on `R` in `Δ*` is `τ` times that in `Δ`). -/
theorem lemma_6_6_5_transform_chain {S : Type*} {Act : Type*} [Fintype S]
    (M : MDC S Act) (τ : ℝ≥0) (hτ0 : 0 < τ) (hτ1 : τ < 1) (e : StationaryPolicy M) :
    let Q := inducedChain M e
    let Q' := inducedChain (transform M τ hτ1.le) (e.toTransform τ hτ1.le)
    -- (i)
    ((∀ x : S, SennottDP.AvgFinite.commClass Q' x = SennottDP.AvgFinite.commClass Q x) ∧
      (∀ x : S, SennottDP.AvgFinite.PositiveRecurrent Q' x ↔ SennottDP.AvgFinite.PositiveRecurrent Q x)) ∧
    -- (ii)
    (∀ x : S, SennottDP.AvgFinite.PositiveRecurrent Q' x → IsAperiodicClass Q' (SennottDP.AvgFinite.commClass Q' x)) ∧
    -- (iii)
    (∀ x : S, SennottDP.AvgFinite.PositiveRecurrent Q x → ∀ j ∈ SennottDP.AvgFinite.commClass Q x,
      SennottDP.AvgFinite.steadyState Q' j = SennottDP.AvgFinite.steadyState Q j ∧
      avgCost (e.toTransform τ hτ1.le).toPolicy j = (τ : ℝ≥0∞) * avgCost e.toPolicy j) := by sorry

end SennottDP.AvgFiniteVI

-- Prove2me | Theorems.Thm_RandomPIGame_lemma_4_5
-- name    : RandomPIGame.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:43.277211+00:00
-- url     : https://prove2.me/theorems/2671be50-5d0c-4f27-8f0b-dae4062ca939
-- title:
--   Lemma 4.5: $\alpha_t=\mathbb P(v_t<k)$ increases to $\mathbb P(v<k)$ and $\alpha_t=f_k^{t+1}(0)$
-- statement:
--   Take $k>0$, and let $\alpha_t=\mathbb P(v_t<k)$, where $v_t(\omega)=v_{\omega_t}$ and $\mathbb P=\mathbb P_p$. Then the sequence $\alpha_0\le\alpha_1\le\cdots$ converges to $\mathbb P(v<k)$. For each $t\in\mathbb N$,
--   $$
--   \alpha_t=f_k^{\,t+1}(0),
--   $$
--   where $f_k^{\,t+1}$ denotes the $(t+1)$-fold iterate of $f_k$.
--
--   So the distribution function of the value of the $t$-truncated game is obtained by iterating the value generating function from $0$, as for the generation-$t$ extinction probabilities of a branching process.
--
--   Differences from the source:
--   - encoding: capacities and thresholds k in [0, ∞) → capacities and thresholds k in ℝ≥0; reason: Lean convention; the same numbers
--   - encoding: P_p is the Borel measure on Ω characterized by (2.4)–(2.5) → gameMeasure p is the pushforward of Measure.infinitePi under g; reason: this is the paper's own construction on p.8; the milestone section2_measure proves g measurable and identifies the two
--   - encoding: a play is a finite or infinite sequence of nodes, and the payoff is the infimum of its capacities → a play is a sequence indexed by ℕ that stays at an end node once reached, and the payoff is the infimum over all stages; reason: stuttering does not change the set of capacities visited
--   - encoding: v_ω is the common value of sup inf and inf sup → value is defined as the sup inf; reason: the equality with inf sup is the milestone section2_value; the strategy types are nonempty and payoffs lie in [0, γ(⊘)], so both real extrema are genuine
--   - encoding: probabilities P(·) → Measure.real, a real number; reason: all measures involved are finite, so nothing is lost
-- source:
--   Flesch, Predtetchinski & Suomala, Random perfect information games, arXiv:2104.10528v1, Lemma 4.5, p.15

import Mathlib
import Definitions.Def_RandomPIGame_Primitive
import Definitions.Def_RandomPIGame_Game
import Definitions.Def_RandomPIGame_Measure
import Definitions.Def_RandomPIGame_Value

open MeasureTheory Filter Topology
open scoped NNReal

namespace RandomPIGame

/-- Let `k > 0` and `α_t = P(v_t < k)`. The sequence `α_0 ≤ α_1 ≤ ⋯` converges to `P(v < k)`, and
`α_t = f_k^{t+1}(0)` for each `t ∈ ℕ`, the `(t + 1)`-fold iterate of `f_k`.
arXiv:2104.10528v1, Lemma 4.5, p.15.

**Formalization Note.** The paper's `β_t = P(v_t ≥ k)` does not occur in the conclusion. -/
theorem lemma_4_5 (p : Measure S) [IsProbabilityMeasure p] (k : ℝ≥0) (hk : 0 < k) :
    Monotone (fun t : ℕ => (gameMeasure p).real {ω : Game | (ω.trunc t).value < k}) ∧
      Tendsto (fun t : ℕ => (gameMeasure p).real {ω : Game | (ω.trunc t).value < k}) atTop
        (𝓝 ((gameMeasure p).real {ω : Game | ω.value < k})) ∧
      ∀ t : ℕ, (gameMeasure p).real {ω : Game | (ω.trunc t).value < k} = (f p k)^[t + 1] 0 := by sorry

end RandomPIGame

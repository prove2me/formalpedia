-- Prove2me | Theorems.Thm_RandomPIGame_theorem_4_6
-- name    : RandomPIGame.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:07.850857+00:00
-- url     : https://prove2.me/theorems/9140485b-23a7-4de2-ba43-4ccff4083fc4
-- title:
--   Theorem 4.6: $\alpha(k)=\mathbb P(v<k)$ is the smallest fixed point of $f_k$
-- statement:
--   Let $p$ be a primitive distribution on $S=\{\mathrm I,\mathrm{II}\}\times[0,\infty)\times\mathbb N$, let $\mathbb P=\mathbb P_p$ be the induced measure on the space of games, and let $v(\omega)=v_\omega$ be the value. For $k>0$ define $\alpha(k)=\mathbb P(v<k)$. Then $\alpha(k)$ is the smallest fixed point of the value generating function $f_k$ on $[0,1]$:
--   $$
--   f_k(\alpha(k))=\alpha(k),\qquad\text{and}\qquad \alpha(k)\le s\ \text{ for every } s\in[0,1]\text{ with } f_k(s)=s.
--   $$
--
--   No assumption is made on $p$: there is no escape model, no independence between the active player and the other coordinates, and no moment condition on $\xi$. This is the main result of the paper. It determines the distribution function of the value from $p$ alone and extends the classical fact that the extinction probability of a branching process is the smallest fixed point of its offspring generating function.
--
--   Differences from the source:
--   - encoding: capacities and thresholds k in [0, ∞) → capacities and thresholds k in ℝ≥0; reason: Lean convention; the same numbers
--   - encoding: P_p is the Borel measure on Ω characterized by (2.4)–(2.5) → gameMeasure p is the pushforward of Measure.infinitePi under g; reason: this is the paper's own construction on p.8; the milestone section2_measure proves g measurable and identifies the two
--   - encoding: a play is a finite or infinite sequence of nodes, and the payoff is the infimum of its capacities → a play is a sequence indexed by ℕ that stays at an end node once reached, and the payoff is the infimum over all stages; reason: stuttering does not change the set of capacities visited
--   - encoding: v_ω is the common value of sup inf and inf sup → value is defined as the sup inf; reason: the equality with inf sup is the milestone section2_value; the strategy types are nonempty and payoffs lie in [0, γ(⊘)], so both real extrema are genuine
--   - encoding: probabilities P(·) → Measure.real, a real number; reason: all measures involved are finite, so nothing is lost
--   - encoding: f_k : [0, 1] → [0, 1]; its fixed points are points of [0, 1] → IsLeast of {x ∈ Set.Icc 0 1 | f p k x = x}; reason: the Lean function f p k is on ℝ, so the fixed points are restricted to [0, 1]
-- source:
--   Flesch, Predtetchinski & Suomala, Random perfect information games, arXiv:2104.10528v1, Theorem 4.6, p.16

import Mathlib
import Definitions.Def_RandomPIGame_Primitive
import Definitions.Def_RandomPIGame_Game
import Definitions.Def_RandomPIGame_Measure
import Definitions.Def_RandomPIGame_Value

open MeasureTheory
open scoped NNReal

namespace RandomPIGame

/-- Let `k > 0`. Then `α(k) = P(v < k)` is the smallest fixed point of the function `f_k` on
`[0, 1]`. arXiv:2104.10528v1, Theorem 4.6, p.16.

**Formalization Note.** `p` is an arbitrary probability measure on `S`: no escape model, no
activation independence, no moment condition on `ξ`. -/
theorem theorem_4_6 (p : Measure S) [IsProbabilityMeasure p] (k : ℝ≥0) (hk : 0 < k) :
    IsLeast {x ∈ Set.Icc (0 : ℝ) 1 | f p k x = x}
      ((gameMeasure p).real {ω : Game | ω.value < k}) := by sorry

end RandomPIGame

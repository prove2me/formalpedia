-- Prove2me | Theorems.Thm_RapidRatePoisson_WeakConv_thinned_simple
-- name    : RapidRatePoisson.WeakConv.thinned_simple
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:18:10.063806+00:00
-- url     : https://prove2.me/theorems/a4a49ae1-2170-41ea-aeb5-46147960f646
-- title:
--   §2, p. 3 — N_ε is a simple point process
-- statement:
--   Let $N$ be a counting path ($N(0)=0$, integer valued, non-decreasing, right-continuous, jumps of size at most one), let $\beta=(\beta_i)_{i\ge1}$ be any $\{0,1\}$-valued mark sequence and let $0<\varepsilon\le1$. Then the thinned, accelerated process
--   $$N_\varepsilon(t)=\sum_{i=1}^{N(t/\varepsilon)}\beta_i,\qquad t\ge0,$$
--   is again a counting path with jumps of size at most one, i.e. a simple point process. Moreover, if every $N(t)$ and every $\beta_i$ is measurable, then every $N_\varepsilon(t)$ is measurable.
--
--   1. The first claim is pathwise: it holds for every $\omega$ whose path of $N$ is a simple counting path, and for every realisation of the marks.
--   2. The second claim makes $N_\varepsilon$ a random element, so that its law on paths is defined.
--
--   This is the first assertion of the sentence that introduces $N_\varepsilon$ on p. 3, and it is the "simple point process" hypothesis of the Poisson limit theorem applied in the proof of Theorem 1.
--
--   **Formalization Note** "Simple counting path" is the published `IsUnitJumpCountingPath` predicate (starts at 0, ℕ-valued, monotone, right-continuous, every jump at most 1). The marks are `Bool`-valued and the sum is the number of indices $1\le i\le N(t/\varepsilon)$ with $\beta_i=$ `true`.
-- source:
--   Zheng, Honnappa & Glynn, arXiv:1807.06805v1, p. 3, §2: "Then, Nǫ = (Nǫ(t) : t ≥ 0) is a simple point process"

import Mathlib
import Definitions.Def_RapidRatePoisson_WeakConv_Model

namespace RapidRatePoisson.WeakConv
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

theorem thinned_simple {Ω : Type*} [MeasurableSpace Ω] (N : ℝ≥0 → Ω → ℝ)
    (β : ℕ → Ω → Bool) (ε : ℝ≥0) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ ω, MartingaleHT.InfiniteServer.IsUnitJumpCountingPath (fun t => N t ω) →
      MartingaleHT.InfiniteServer.IsUnitJumpCountingPath (fun t => thinned N β ε t ω)) ∧
    ((∀ t, Measurable (N t)) → (∀ i, 1 ≤ i → Measurable (β i)) →
      ∀ t, Measurable (thinned N β ε t)) := by sorry

end RapidRatePoisson.WeakConv

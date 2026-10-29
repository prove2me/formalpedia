-- Prove2me | Theorems.Thm_PutermanMDP_SemiMarkov_stationary_ratio
-- name    : PutermanMDP.SemiMarkov.stationary_ratio
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:51.893078+00:00
-- url     : https://prove2.me/theorems/40d4ce74-5c5a-4d3e-8099-5c7e892318e7
-- title:
--   Proposition 11.4.1 — stationary semi-Markov reward ratio
-- statement:
--   Let $S$ be nonempty and countable, and fix a stationary randomized rule $d$ in a semi-Markov model satisfying Assumption 11.1.1. Suppose the Cesaro limit $M_d^*$ exists and is a transition probability matrix. All finite-epoch expectations and the two limiting matrix products below are interpreted as finite, absolutely convergent expectations. Then the reward ratios converge and
--   $$g^{d^\infty}(s)=\lim_{n\to\infty}R_n^d(s)=\frac{(M_d^*r_d)(s)}{(M_d^*y_d)(s)}.$$
--   If the embedded chain is unichain, this gain is one real constant independent of the initial state.
--
--   This is the source's stationary reward-ratio representation. Its literal countable-state claim is retained despite finding F3, which supplies a counterexample with unbounded mean holding times.
--
--   **Formalization Note** Absolute summability makes explicit the finite-real domain of the displayed expectations and matrix products; no uniform boundedness of $r_d$ or $y_d$ is imposed. The gain itself uses an extended-real liminf, and the conclusion asserts equality with a real limit.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, https://doi.org/10.1002/9780470316887, p. 551 (PDF 567), Proposition 11.4.1

import Definitions.Def_PutermanMDP_SemiMarkov_Stationary

open Filter
open scoped Topology

namespace PutermanMDP.SemiMarkov

theorem stationary_ratio {S : Type*} [Countable S] [Nonempty S]
    (M : Model S) (d : Rule M) (hNE : Nonexplosive M)
    (hP : CesaroProbability M d) (hE : FiniteEpochMoments M d)
    (hL : FiniteLimitMoments M d) :
    ((∀ s, Tendsto (fun n => rewardRatio M d n s) atTop
        (𝓝 (limitingRatio M d s))) ∧
      (∀ s, gain M d s = (limitingRatio M d s : EReal))) ∧
    (Unichain M d → ∃ g : ℝ, ∀ s, gain M d s = (g : EReal)) := by sorry

end PutermanMDP.SemiMarkov

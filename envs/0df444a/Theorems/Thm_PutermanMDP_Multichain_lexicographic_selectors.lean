-- Prove2me | Theorems.Thm_PutermanMDP_Multichain_lexicographic_selectors
-- name    : PutermanMDP.Multichain.lexicographic_selectors
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T03:00:26.273005+00:00
-- url     : https://prove2.me/theorems/2262a7ad-49cd-41bb-bfa0-74cae9a21575
-- title:
--   Theorem 9.1.7 — optimality of lexicographic selectors
-- statement:
--   Let $S$ and every $A_s$ be finite, with the stationary reward model and all history-dependent randomized comparator policies.
--
--   1. If vectors $g,h$ satisfy the multichain optimality equations and $d^*$ satisfies $P_{d^*}g=g$ and maximizes $r_d+P_dh$ over $E=\{d:P_dg=g\}$, then $(d^*)^\infty$ is average optimal.
--   2. If $g,h$ satisfy the modified optimality equations, $P_{d^*}g=g$, and $d^*$ maximizes $r_d+P_dh$ over all admissible deterministic rules, then $(d^*)^\infty$ is average optimal.
--
--   In both cases the conclusion is
--   $$g_-^{(d^*)^\infty}(s)\ge g_+^\pi(s)\quad\text{for every }s\in S\text{ and every }\pi\in\Pi^{HR}.$$
--   The theorem certifies policies selected from either equation system, with the appropriate maximizing domain.
--
--   **Formalization Note** Maxima and vector inequalities are componentwise. Nonempty states and available actions implement the standing model convention. Real vectors on finite states are automatically bounded.
-- source:
--   Puterman, Markov Decision Processes: Discrete Stochastic Dynamic Programming, Wiley, 1994, https://doi.org/10.1002/9780470316887, p. 450 (PDF 466), Theorem 9.1.7

import Mathlib
import Definitions.Def_PutermanMDP_Multichain_Criteria

open MarkovDecisionProcesses Filter
open scoped Topology

namespace PutermanMDP.Multichain

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A] [Nonempty S]

/-- Theorem 9.1.7, p. 450 (PDF 466), both parts. -/
theorem lexicographic_selectors (M : StationaryMDP S A) :
    (∀ (g h : S → ℝ) (d : Rule M), OptimalityEquations M g h →
      RestrictedSelector M g h d → IsAverageOptimal (policy M d)) ∧
    (∀ (g h : S → ℝ) (d : Rule M), ModifiedEquations M g h →
      InE M g d → FullSelector M h d → IsAverageOptimal (policy M d)) := by sorry

end PutermanMDP.Multichain

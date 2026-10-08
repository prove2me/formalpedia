-- Prove2me | Theorems.Thm_ServiceParts_Shortfall_discrete_transition_probabilities
-- name    : ServiceParts.Shortfall.discrete_transition_probabilities
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T23:35:44.745644+00:00
-- url     : https://prove2.me/theorems/7f64b6d0-b39c-4aa8-86f6-a2f69dd0ea46
-- title:
--   Section 8.1.2 — with integer demand the shortfall is a Markov chain with transition probabilities p_ij
-- statement:
--   In the discrete-demand shortfall model (integer capacity $c$, nonnegative integer i.i.d. demands $D_1, D_2, \dots$ with generic demand $D$), let $V_0 = 0$ and $V_n = [V_{n-1} + D_n - c]^+$. Then $(V_n)$ is a Markov chain with the transition probabilities
--   $$p_{ij} = \begin{cases} P\{D \le c - i\}, & j = 0 \text{ and } i \le c,\\ P\{D = c + (j - i)\}, & j > 0,\ i \le c + j,\\ 0, & \text{otherwise,}\end{cases}$$
--   in the following sense: for every $n \ge 0$, every sequence of states $x_0, x_1, \dots, x_n$ and every state $j$,
--   $$P\{V_0 = x_0, \dots, V_n = x_n,\ V_{n+1} = j\} = P\{V_0 = x_0, \dots, V_n = x_n\}\cdot p_{x_n j}.$$
--
--   This is the basis of the exact computation of the shortfall distribution by the stationary equations of the chain.
--
--   **Formalization Note** The Markov property and the transition matrix are stated together as a factorisation of path probabilities, which avoids conditioning on events of probability zero. The first case of $p_{ij}$ is as printed; for $i > c$ the event $V_n = 0$ is impossible because $D \ge 0$, consistent with the "otherwise" case.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 185, Section 8.1.2 (transition probabilities p_ij)

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_DiscreteShortfallModel

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Shortfall

/-- Section 8.1.2, p. 185. With integer demand, the shortfall process `V_0 = 0`,
`V_n = [V_{n−1} + D_n − c]^+` is a Markov chain with transition probabilities `p_{ij}`: for every
`n`, every path `x_0, …, x_n` and every state `j`,
`P{V_0 = x_0, …, V_n = x_n, V_{n+1} = j} = P{V_0 = x_0, …, V_n = x_n} · p_{x_n j}`. -/
theorem discrete_transition_probabilities {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : DiscreteShortfallModel Ω P) (n : ℕ) (x : ℕ → ℕ) (j : ℕ) :
    (P {ω | (∀ k ≤ n, M.shortfall k ω = x k) ∧ M.shortfall (n + 1) ω = j}).toReal =
      (P {ω | ∀ k ≤ n, M.shortfall k ω = x k}).toReal * M.transProb (x n) j := by sorry

end ServiceParts.Shortfall

-- Prove2me | Theorems.Thm_SennottDP_AvgFiniteVI_prop_6_5_1_acoe_solutions
-- name    : SennottDP.AvgFiniteVI.prop_6_5_1_acoe_solutions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T09:31:41.906698+00:00
-- url     : https://prove2.me/theorems/f25fff0b-7150-4819-b219-89657564353b
-- title:
--   Proposition 6.5.1 — any solution of the ACOE yields the minimum average cost and optimal policies
-- statement:
--   Let $\Delta$ be an MDC with finite state space $S$, $F$ a real constant and $r : S \to \mathbb R$.
--
--   1. If
--   $$F + r(i) \ge \min_a\Big\{C(i,a) + \sum_j P_{ij}(a) r(j)\Big\}, \qquad i \in S, \tag{6.36}$$
--   and $e$ realizes the minimum, then $J_e(i) \le F$ for all $i$. If moreover $F \le J_\theta(i)$ for every policy $\theta$ and state $i$, then $J \equiv F$ and $e$ is average cost optimal.
--   2. If
--   $$F + r(i) = \min_a\Big\{C(i,a) + \sum_j P_{ij}(a) r(j)\Big\}, \qquad i \in S, \tag{6.37}$$
--   then $J \equiv F$ and every stationary policy realizing the minimum is average cost optimal. With $f$ as in Proposition 6.2.3, distinguished states $z_k$ of its positive recurrent classes $R_k$, reaching probabilities $p_k(i)$, and $h$ as in Theorem 6.4.2: $r(i) = h(i) + r(z_k) - h(z_k)$ for $i \in R_k$, and $r(i) \le h(i) + \sum_k p_k(i)[r(z_k) - h(z_k)]$ for $i$ transient under $f$.
--   3. If (6.37) holds, $e$ realizes the minimum, $e$ and $f$ are unichain with a common positive recurrent state $x$, $h$ uses $x$ as distinguished state, and $r(x) = 0$, then $r(i) = h(i) = c_{ix}(e) - J m_{ix}(e)$ for all $i$.
--
--   The proposition says that solving the ACOE by any means gives the minimum average cost and an optimal policy, and describes how far a solution can differ from $h$.
--
--   **Formalization Note** $J_e \le F$ is stated in $[0,\infty]$ as $J_e(i) \le \max(F,0)$; since costs are nonnegative, (6.36) with a minimizer forces $F \ge 0$ anyway. In part 3, $J = F$ by part 2.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 112, Proposition 6.5.1, Eqs. (6.36)–(6.37)

import Mathlib
import Definitions.Def_SennottDP_AvgFiniteVI_ACOE

namespace SennottDP.AvgFiniteVI

open scoped ENNReal NNReal

/-- Proposition 6.5.1 (Sennott, p. 112). Let `Δ` be an MDC with a finite state space `S`, and let
`F` be a finite constant and `r` a finite function.
(i) If `F + r(i) ≥ min_a {C(i,a) + ∑_j P_{ij}(a) r(j)}` (6.36) and `e` realizes the minimum, then
`J_e(i) ≤ F`; if moreover `F` is a lower bound on the average costs, then the minimum average cost
equals `F` and `e` is average cost optimal.
(ii) If `F + r(i) = min_a {C(i,a) + ∑_j P_{ij}(a) r(j)}` (6.37), then the minimum average cost
equals `F` and every stationary policy realizing the minimum is average cost optimal. With `f` as
in Proposition 6.2.3, distinguished states `z_k` of its positive recurrent classes `R_k`, and `h` as
in Theorem 6.4.2: `r(i) = h(i) + r(z_k) − h(z_k)` for `i ∈ R_k`, and
`r(i) ≤ h(i) + ∑_k p_k(i)[r(z_k) − h(z_k)]` for `i` transient under `f`.
(iii) If (6.37) holds, `e` realizes the minimum, `e` and `f` are unichain with common positive
recurrent state `x`, `x` is the distinguished state of `h`, and `r(x) = 0`, then
`r(i) = h(i) = c_{ix}(e) − J m_{ix}(e)` for all `i` (here `J = F`). -/
theorem prop_6_5_1_acoe_solutions {S : Type*} {Act : Type*} [Fintype S]
    (M : MDC S Act) (F : ℝ) (r : S → ℝ) :
    -- (i)
    ((∀ i : S, bellmanMin M r i ≤ F + r i) →
      ∀ e : StationaryPolicy M, RealizesMin M r e →
        (∀ i : S, avgCost e.toPolicy i ≤ ENNReal.ofReal F) ∧
        ((∀ (θ : Policy M) (i : S), ENNReal.ofReal F ≤ avgCost θ i) →
          (∀ i : S, avgValue M i = ENNReal.ofReal F) ∧ IsAverageOptimal e.toPolicy)) ∧
    -- (ii)
    ((∀ i : S, F + r i = bellmanMin M r i) →
      (∀ i : S, avgValue M i = ENNReal.ofReal F) ∧
      (∀ e : StationaryPolicy M, RealizesMin M r e → IsAverageOptimal e.toPolicy) ∧
      ∀ (f : StationaryPolicy M) (α₀ : ℝ), α₀ ∈ Set.Ioo (0 : ℝ) 1 →
        (∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α) →
        ∀ (Z : Finset S), SennottDP.AvgFinite.IsDistinguishedSet (inducedChain M f) Z → ∀ z : S,
          (∀ zk ∈ Z, ∀ i ∈ SennottDP.AvgFinite.commClass (inducedChain M f) zk,
            r i = hLim M z i + r zk - hLim M z zk) ∧
          (∀ i : S, IsTransient (inducedChain M f) i →
            r i ≤ hLim M z i + ∑ zk ∈ Z, (classReachProb M f zk i).toReal *
              (r zk - hLim M z zk))) ∧
    -- (iii)
    ((∀ i : S, F + r i = bellmanMin M r i) →
      ∀ e : StationaryPolicy M, RealizesMin M r e →
      ∀ (f : StationaryPolicy M) (α₀ : ℝ), α₀ ∈ Set.Ioo (0 : ℝ) 1 →
        (∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α) →
        ∀ x : S, IsUnichain (inducedChain M e) → IsUnichain (inducedChain M f) →
          SennottDP.AvgFinite.PositiveRecurrent (inducedChain M e) x → SennottDP.AvgFinite.PositiveRecurrent (inducedChain M f) x →
          r x = 0 →
          ∀ i : S, r i = hLim M x i ∧
            hLim M x i = (condPassCost M e x i).toReal - F * (condPassTime M e x i).toReal) := by sorry

end SennottDP.AvgFiniteVI

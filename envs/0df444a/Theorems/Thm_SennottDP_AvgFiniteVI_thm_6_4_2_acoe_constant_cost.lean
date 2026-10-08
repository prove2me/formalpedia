-- Prove2me | Theorems.Thm_SennottDP_AvgFiniteVI_thm_6_4_2_acoe_constant_cost
-- name    : SennottDP.AvgFiniteVI.thm_6_4_2_acoe_constant_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T09:31:33.972712+00:00
-- url     : https://prove2.me/theorems/580788a9-e834-4be8-a1c1-7db767b5713c
-- title:
--   Theorem 6.4.2 — the average cost optimality equation under constant minimum average cost
-- statement:
--   Let $\Delta$ be an MDC with finite state space $S$ whose minimum average cost is constant, $J(i) \equiv J$. Let $f$ be a stationary policy that is $\alpha$ discount optimal for all $\alpha \in (\alpha_0,1)$ (Proposition 6.2.3), and let $w^*$ be built from $f$ and a choice of distinguished states of its positive recurrent classes (Section 6.3). Fix a distinguished state $z$ and put $h_\alpha(i) = V_\alpha(i) - V_\alpha(z)$. Then:
--
--   1. $\lim_{\alpha\to1^-} h_\alpha(i) =: h(i)$ exists and equals $w^*(i) - w^*(z)$;
--   2. the **average cost optimality equation**
--   $$J + h(i) = \min_a\Big\{C(i,a) + \sum_j P_{ij}(a) h(j)\Big\}, \qquad i \in S, \tag{6.31}$$
--   holds, and $f$ realizes the minimum;
--   3. every stationary $e$ realizing the minimum in (6.31) is average cost optimal, and $\lim_n E_e[h(X_n) \mid X_0 = i]/n = 0$;
--   4. with $d_n(i) = h(i) + nJ - v_n(i)$ ($v_n$ the minimum $n$-horizon cost, terminal cost $0$), $|d_n| \le L$ for every $L$ bounding $|h_\alpha(i)|$ over $i \in S$, $\alpha \in (0,1)$;
--   5. $\lim_n v_n(i)/n = J$;
--   6. if $f$ is unichain and $z$ is positive recurrent under $f$ (the distinguished state of its class), then $h(i) = w(i) = c_{iz}(f) - J m_{iz}(f)$.
--
--   This is the ACOE for multichain models with constant minimal cost, and part 4 is the bound that drives value iteration.
--
--   **Formalization Note** $h$ is the defined limit (`hLim`); part 1 asserts existence. In part 6, $w$ is computed with the single distinguished state $z$, and $c_{iz}$, $m_{iz}$ are the expected cost and time to reach $z$ (reached with probability one).
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 109–110, Theorem 6.4.2, Eq. (6.31)

import Mathlib
import Definitions.Def_SennottDP_AvgFiniteVI_ACOE

namespace SennottDP.AvgFiniteVI

open scoped ENNReal NNReal Topology
open Filter

/-- Theorem 6.4.2 (Sennott, pp. 109–110). Let `S` be finite and assume `J(i) ≡ J`. Let `f`, `α₀`
be as in Proposition 6.2.3, let `Z` contain one distinguished state from each positive recurrent
class of the chain induced by `f` (Section 6.3), and fix a distinguished state `z`; let
`h_α(i) = V_α(i) − V_α(z)`.
(i) `lim_{α→1⁻} h_α(i) =: h(i) = w*(i) − w*(z)`;
(ii) the ACOE `J + h(i) = min_a {C(i,a) + ∑_j P_{ij}(a) h(j)}` (6.31) holds and `f` realizes the
minimum;
(iii) a stationary `e` realizing the minimum in (6.31) is average cost optimal, and
`lim_n E_e[h(X_n) | X_0 = i]/n = 0`;
(iv) with `d_n(i) = h(i) + nJ − v_n(i)`, `|d_n| ≤ L` for every bound `L` of `|h_α|`;
(v) `lim_n v_n(i)/n = J`;
(vi) if `f` is unichain and `z` is the distinguished state of its positive recurrent class, then
`h(i) = w(i) = c_{iz}(f) − J m_{iz}(f)`. -/
theorem thm_6_4_2_acoe_constant_cost {S : Type*} {Act : Type*} [Fintype S]
    (M : MDC S Act) (J : ℝ≥0) (hJ : ∀ i : S, avgValue M i = J)
    (f : StationaryPolicy M) (α₀ : ℝ) (hα₀ : α₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hf : ∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α)
    (Z : Finset S) (hZ : SennottDP.AvgFinite.IsDistinguishedSet (inducedChain M f) Z) (z : S) :
    -- (i)
    (∀ i : S, Tendsto (fun α : ℝ => hDisc M z α i) (𝓝[<] 1) (𝓝 (hLim M z i)) ∧
      hLim M z i = relValueNorm M f Z i - relValueNorm M f Z z) ∧
    -- (ii)
    ((∀ i : S, (J : ℝ) + hLim M z i = bellmanMin M (hLim M z) i) ∧
      RealizesMin M (hLim M z) f) ∧
    -- (iii)
    (∀ e : StationaryPolicy M, RealizesMin M (hLim M z) e →
      IsAverageOptimal e.toPolicy ∧
      ∀ i : S, Tendsto (fun n : ℕ => expectStat M e (hLim M z) n i / n) atTop (𝓝 0)) ∧
    -- (iv)
    (∀ L : ℝ, (∀ i : S, ∀ α ∈ Set.Ioo (0 : ℝ) 1, |hDisc M z α i| ≤ L) →
      ∀ (n : ℕ) (i : S), |dSeq M z J n i| ≤ L) ∧
    -- (v)
    (∀ i : S, Tendsto (fun n : ℕ => (horizonValue M n i).toReal / n) atTop (𝓝 (J : ℝ))) ∧
    -- (vi)
    (IsUnichain (inducedChain M f) → SennottDP.AvgFinite.PositiveRecurrent (inducedChain M f) z →
      ∀ i : S, hLim M z i = relValue M f {z} i ∧
        relValue M f {z} i =
          (condPassCost M f z i).toReal - (J : ℝ) * (condPassTime M f z i).toReal) := by sorry

end SennottDP.AvgFiniteVI

-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_theorem_4
-- name    : SpreadBetting.Inertial.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:19.097732+00:00
-- url     : https://prove2.me/theorems/15b9ed15-c932-43ec-a2a8-7485bb3798fa
-- title:
--   Theorem 4, p. 17 — under the inertial policy with r ∈ (0, r̄): Z_t → ±∞ a.s., Σ E𝔡_t = O(√(T log T)) and diverges, regret O(log T)
-- statement:
--   Let the market satisfy the standing assumptions, let $c \in (0,1)$, and let the market maker use the inertial policy $\pi_I$ with $\rho(z) = 1/(r_0 + rz)$ and $r \in (0, \bar r)$, $\bar r$ the explicit bound (G.2). Let $\bar z$ be the threshold (G.1) and $\xi_i^*$ the informed bettor's threshold strategy (4.4). Write $\mathfrak d_t := |s_t - m_i|$ for the distance of the spread line to the true median. Then:
--
--   0. (from (T3:2)) $\bar z \in \mathbb Z \cup \{-\infty\}$, and $\xi_i^*$ is the informed bettor's best response (2.3) for each $i \in \{0,1\}$.
--   1. (T4:1) $Z_t \to \infty$ almost surely under $\mathbb P_1^{\pi_I,\xi_1^*}$ and $Z_t \to -\infty$ almost surely under $\mathbb P_0^{\pi_I,\xi_0^*}$; as a result $\mathfrak d_t \to 0$ almost surely under $\mathbb P_i^{\pi_I,\xi_i^*}$.
--   2. (T4:2) For each $i$, $\sum_t \mathbb E_i^{\pi_I,\xi_i^*}[\mathfrak d_t]$ diverges, at a rate
--   $$
--   \sum_{t=1}^T \mathbb E_i^{\pi_I,\xi_i^*}[\mathfrak d_t] = O\big(\sqrt{T\log T}\big).
--   $$
--   3. (T4:3) The worst-case regret $\Delta^{\pi_I}(T) = \max\{\Delta_0^{\pi_I,\xi_0^*}(T), \Delta_1^{\pi_I,\xi_1^*}(T)\}$ satisfies
--   $$
--   \Delta^{\pi_I}(T) = O(\log T).
--   $$
--
--   The inertial policy thus deters bluffing by the informed bettor, drives the spread line to the correct median at a sub-exponential rate, and loses only logarithmically against the clairvoyant market maker.
--
--   **Formalization Note** Theorem 4's probability $\mathbb P_i^{\pi_I,\xi_i^*}$ is defined by the best response $\xi_i^*$; pinning $\xi_i^*$ to the threshold strategy at $\bar z$ of (G.1) is faithful only together with the fact that it is a best response, so part 0 (clause (T3:2) of Theorem 3) is included. The almost-sure clauses use the path law `markovChainMeasure` of the market-state kernel from $Z_1 = 0$ (coordinate $t$ is $Z_{t+1}$). Expectations are exact finite recursions over bet histories. "Diverges at rate $O(g)$" is divergence to $+\infty$ together with Definition 1. $\bar r$ is the explicit (G.2) rather than an existential constant.
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 17, Theorem 4 (with Theorem 3, (T3:2)); (G.1)–(G.4) p. 49

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model
import Definitions.Def_SpreadBetting_Inertial_Chain
import Definitions.Def_GittinsIndex

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem theorem_4 (M : Market) (hM : M.Standing) (r : ℝ) (hr0 : 0 < r) (hr : r < rbar M) :
    let ρp := rhoIP M r
    -- (0) = (T3:2): z̄ ∈ ℤ ∪ {-∞}, and ξ*_i of (4.4) is a best response (2.3)
    ((zbarSet M ρp).Nonempty ∧ ∀ i : Fin 2, IsBestResponse M ρp i (xiStar M ρp i)) ∧
    -- (T4:1)
    (∀ᵐ ω ∂(BanditAlgorithm.markovChainMeasure (chainKernel M ρp 1 (xiStar M ρp 1)) 0),
      Tendsto ω atTop atTop ∧ Tendsto (fun t => |sTilde M ρp (ω t) - M.m1|) atTop (𝓝 0)) ∧
    (∀ᵐ ω ∂(BanditAlgorithm.markovChainMeasure (chainKernel M ρp 0 (xiStar M ρp 0)) 0),
      Tendsto ω atTop atBot ∧ Tendsto (fun t => |sTilde M ρp (ω t) - M.m0|) atTop (𝓝 0)) ∧
    -- (T4:2)
    (∀ i : Fin 2,
      Tendsto (fun T : ℕ => cumExp M ρp i (xiStar M ρp i)
        (fun z _ _ => |sTilde M ρp z - med M i|) T [] 0) atTop atTop ∧
      IsBigOP (fun T : ℕ => cumExp M ρp i (xiStar M ρp i)
          (fun z _ _ => |sTilde M ρp z - med M i|) T [] 0)
        (fun T : ℕ => Real.sqrt (T * Real.log T))) ∧
    -- (T4:3)
    IsBigOP (fun T : ℕ => max (regret M ρp 0 (xiStar M ρp 0) T) (regret M ρp 1 (xiStar M ρp 1) T))
      (fun T : ℕ => Real.log T) := by sorry

end SpreadBetting.Inertial

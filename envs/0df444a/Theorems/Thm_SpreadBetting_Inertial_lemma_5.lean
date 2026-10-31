-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_lemma_5
-- name    : SpreadBetting.Inertial.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:22.296252+00:00
-- url     : https://prove2.me/theorems/88f6b746-9c11-44b8-9749-36d4e55d01cf
-- title:
--   Lemma 5, p. 22 — the regret of IP is Δ^{π_I}(T) = Σ_{t≤T} E⁰₁[l(Z_t)] with l(z) = (2 − c)ρ(z)I{z < z̄} + (4 − 2c)ρ²(z)I{z ≥ z̄}
-- statement:
--   Let the market satisfy the standing assumptions and $\rho(z) = 1/(r_0 + rz)$ with $r \in (0, \bar r)$, and let the informed bettor use $\xi_i^*$ of (4.4). Then for every $T$,
--   $$
--   \Delta^{\pi_I}(T) = \max\big\{\Delta_0^{\pi_I,\xi_0^*}(T), \Delta_1^{\pi_I,\xi_1^*}(T)\big\} = \sum_{t=1}^T \mathbb E_1^0[l(Z_t)], \tag{4.12}
--   $$
--   where
--   $$
--   l(z) = (2-c)\rho(z)\,\mathbb I\{z < \bar z\} + (4-2c)\rho^2(z)\,\mathbb I\{z \ge \bar z\}. \tag{4.13}
--   $$
--   In fact each of the two regrets $\Delta_i^{\pi_I,\xi_i^*}(T)$ equals the right-hand side.
--
--   The lemma turns regret into an additive functional of the market state, to which Lemma 4 applies.
--
--   **Formalization Note** The lemma is stated in the context of Theorem 4, so $r \in (0, \bar r)$ is in force. The clause that both regrets equal the sum is the content of the paper's proof (p. 59) and implies the printed statement.
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 22, Lemma 5, (4.12)–(4.13); proof p. 59

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_5 (M : Market) (hM : M.Standing) (r : ℝ) (hr0 : 0 < r) (hr : r < rbar M) :
    let ρp := rhoIP M r
    let L : ℕ → ℝ := fun T => cumExp M ρp 1 (xiStar M ρp 1)
      (fun z _ _ => lossFn M ρp (belowZbar M ρp) z) T [] 0
    ∀ T : ℕ, max (regret M ρp 0 (xiStar M ρp 0) T) (regret M ρp 1 (xiStar M ρp 1) T) = L T ∧
      ∀ i : Fin 2, regret M ρp i (xiStar M ρp i) T = L T := by sorry

end SpreadBetting.Inertial

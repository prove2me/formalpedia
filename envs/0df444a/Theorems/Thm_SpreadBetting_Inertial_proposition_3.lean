-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_proposition_3
-- name    : SpreadBetting.Inertial.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:09.115778+00:00
-- url     : https://prove2.me/theorems/82b28ee4-924f-48b5-a199-6ff4bd4e368a
-- title:
--   Proposition 3, p. 23 — under IP with r ∈ (0, r̄): Σ_t E⁰₁ I{Z_t ≤ M} converges, Σ_t E⁰₁ ρ(Z_t) = O(√(T log T)), Σ_t E⁰₁ l(Z_t) = O(log T), both divergent
-- statement:
--   Let the market satisfy the standing assumptions, $c \in (0,1)$, and $\rho(z) = 1/(r_0 + rz)$ with $r \in (0, \bar r)$. Under $H_1$, the inertial policy and the informed bettor's threshold strategy $\xi_1^*$, with expectations $\mathbb E_1^0$ from $Z_1 = 0$:
--
--   1. (P3:1) For all sufficiently large $M$, $\sum_t \mathbb E_1^0[\mathbb I\{Z_t \le M\}]$ converges.
--   2. (P3:2) $\sum_t \mathbb E_1^0[\rho(Z_t)]$ diverges, at a rate
--   $$
--   \sum_{t=1}^T \mathbb E_1^0[\rho(Z_t)] = O\big(\sqrt{T\log T}\big).
--   $$
--   3. (P3:3) $\sum_t \mathbb E_1^0[l(Z_t)]$ diverges, at a rate $\sum_{t=1}^T \mathbb E_1^0[l(Z_t)] = O(\log T)$, with $l$ the loss (4.13).
--
--   These are the three steps behind Theorem 4: almost-sure convergence of the spread lines, their rate, and logarithmic regret.
--
--   **Formalization Note** $\rho(Z_t)$ uses the extension (E.1) of $\rho$ to $\mathbb Z$. $O(\cdot)$ is Definition 1.
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 23, Proposition 3; (4.13) p. 22

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model
import Definitions.Def_SpreadBetting_Inertial_Chain

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem proposition_3 (M : Market) (hM : M.Standing) (r : ℝ) (hr0 : 0 < r)
    (hr : r < rbar M) :
    let ρp := rhoIP M r
    let ξ := xiStar M ρp 1
    -- (P3:1)
    (∃ M₀ : ℤ, ∀ Mx : ℤ, M₀ ≤ Mx → ∃ L : ℝ,
      Tendsto (fun T : ℕ => cumExp M ρp 1 ξ (fun z _ _ => indic (z ≤ Mx)) T [] 0) atTop (𝓝 L)) ∧
    -- (P3:2)
    (Tendsto (fun T : ℕ => cumExp M ρp 1 ξ (fun z _ _ => rhoExt M ρp z) T [] 0) atTop atTop ∧
      IsBigOP (fun T : ℕ => cumExp M ρp 1 ξ (fun z _ _ => rhoExt M ρp z) T [] 0)
        (fun T : ℕ => Real.sqrt (T * Real.log T))) ∧
    -- (P3:3)
    (Tendsto (fun T : ℕ => cumExp M ρp 1 ξ (fun z _ _ => lossFn M ρp (belowZbar M ρp) z) T [] 0)
        atTop atTop ∧
      IsBigOP (fun T : ℕ => cumExp M ρp 1 ξ (fun z _ _ => lossFn M ρp (belowZbar M ρp) z) T [] 0)
        (fun T : ℕ => Real.log T)) := by sorry

end SpreadBetting.Inertial

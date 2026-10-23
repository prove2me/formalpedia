-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_proposition_K_2
-- name    : SpreadBetting.Inertial.proposition_K_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:09.995321+00:00
-- url     : https://prove2.me/theorems/7a1f33b3-6ba9-46f6-9d98-76f25971f5a7
-- title:
--   Proposition K.2, p. 69 — slowly vanishing ρ, Z̄-threshold strategy: Σ_t Ẽ⁰₁ I{Z_t ≤ M} converges, Z_t → ∞ a.s., loss and regret diverge at rate O(Σ_{t≤T} ρ(t)) if ρ is regular
-- statement:
--   Let the market satisfy the standing assumptions, let $\rho : \mathbb Z_+ \to (0, \tfrac12-\alpha)$ be slowly vanishing, extended by (E.1), and let $\bar Z \in \mathbb Z \cup \{-\infty\}$. Let the informed bettor use the $\bar Z$-threshold strategy $\xi_i^{\bar Z}$ (Definition 4), and write $\tilde{\mathbb P}_1^0, \tilde{\mathbb E}_1^0$ for the law and expectation under $H_1$ from $Z_1 = 0$, $\tilde l$ for the loss (L.4) and $\tilde\Delta^{\pi_I}(T) = \max_i \Delta_i^{\pi_I,\xi_i^{\bar Z}}(T)$. Then:
--
--   1. (PK.2:1) For all sufficiently large $M$, $\sum_t \tilde{\mathbb E}_1^0[\mathbb I\{Z_t \le M\}]$ converges.
--   2. (PK.2:2) $Z_t \to \infty$ $\tilde{\mathbb P}_1^0$-almost surely; hence $|s_t - m_1| \to 0$ almost surely.
--   3. (PK.2:3) If $\rho$ is regular, $\sum_t \tilde{\mathbb E}_1^0[\tilde l(Z_t)]$ diverges, at a rate $\sum_{t=1}^T \tilde{\mathbb E}_1^0[\tilde l(Z_t)] = O\big(\sum_{t=1}^T\rho(t)\big)$.
--   4. (PK.2:4) If $\rho$ is regular, $\tilde\Delta^{\pi_I}(T)$ diverges, at a rate $\tilde\Delta^{\pi_I}(T) = O\big(\sum_{t=1}^T \rho(t)\big)$.
--
--   This generalizes Proposition 3 and Theorem 4 from $\rho(z) = 1/(r_0+rz)$ and $\bar z$ to any slowly vanishing $\rho$ and any threshold.
--
--   **Formalization Note** The almost-sure clause uses the path law `markovChainMeasure` of the market-state kernel started at $0$ (coordinate $t$ is $Z_{t+1}$). "Converges" for a nonnegative partial-sum sequence is stated as convergence to a real limit; "diverges at rate $O(g)$" as divergence to $+\infty$ together with Definition 1. $\bar Z = -\infty$ is `⊥` in `WithBot ℤ`.
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 69, Proposition K.2; Definition 4 and K.1 p. 68; (L.4)–(L.5) p. 71

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model
import Definitions.Def_SpreadBetting_Inertial_Chain
import Definitions.Def_GittinsIndex

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem proposition_K_2 (M : Market) (hM : M.Standing) (ρp : ℕ → ℝ)
    (hsv : SlowlyVanishing M ρp) (Zbar : WithBot ℤ) :
    let ξ1 := threshStrat 1 (belowWB Zbar)
    let ξ0 := threshStrat 0 (belowWB Zbar)
    let Ls : ℕ → ℝ := fun T => cumExp M ρp 1 ξ1 (fun z _ _ => lossFn M ρp (belowWB Zbar) z) T [] 0
    let R : ℕ → ℝ := fun T => max (regret M ρp 0 ξ0 T) (regret M ρp 1 ξ1 T)
    -- (PK.2:1)
    (∃ M₀ : ℤ, ∀ Mx : ℤ, M₀ ≤ Mx → ∃ L : ℝ,
      Tendsto (fun T : ℕ => cumExp M ρp 1 ξ1 (fun z _ _ => indic (z ≤ Mx)) T [] 0) atTop (𝓝 L)) ∧
    -- (PK.2:2)
    (∀ᵐ ω ∂(BanditAlgorithm.markovChainMeasure (chainKernel M ρp 1 ξ1) 0),
      Tendsto ω atTop atTop ∧ Tendsto (fun t => |sTilde M ρp (ω t) - M.m1|) atTop (𝓝 0)) ∧
    -- (PK.2:3)
    (Regular ρp → Tendsto Ls atTop atTop ∧
      IsBigOP Ls (fun T : ℕ => ∑ t ∈ Finset.Icc 1 T, ρp t)) ∧
    -- (PK.2:4)
    (Regular ρp → Tendsto R atTop atTop ∧
      IsBigOP R (fun T : ℕ => ∑ t ∈ Finset.Icc 1 T, ρp t)) := by sorry

end SpreadBetting.Inertial

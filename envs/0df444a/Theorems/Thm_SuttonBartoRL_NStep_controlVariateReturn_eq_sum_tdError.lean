-- Prove2me | Theorems.Thm_SuttonBartoRL_NStep_controlVariateReturn_eq_sum_tdError
-- name    : SuttonBartoRL.NStep.controlVariateReturn_eq_sum_tdError
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:58:35.97832+00:00
-- url     : https://prove2.me/theorems/a0129657-89f6-41dc-911a-44ecf6e11cba
-- title:
--   The off-policy return (7.13) as a sum of TD errors (Exercise 7.8)
-- statement:
--   Consider a sample path $S_t, A_t, R_{t+1}, S_{t+1}, \dots$, a target policy $\pi$, a behavior policy $b$, the ratios $\rho_i = \pi(A_i \mid S_i)/b(A_i \mid S_i)$, a discount $\gamma$, and a state-value estimate $V$ that does not change. Let $G_{t:h}$ be the off-policy $n$-step return with control variate (7.13), $G_{t:h} = \rho_t (R_{t+1} + \gamma G_{t+1:h}) + (1-\rho_t) V(S_t)$, $G_{h:h} = V(S_h)$, and $\delta_k = R_{k+1} + \gamma V(S_{k+1}) - V(S_k)$ the TD error (6.5). Then for every $t \le h$,
--   $$G_{t:h} - V(S_t) = \sum_{k=t}^{h-1} \gamma^{k-t} \Big(\prod_{i=t}^{k} \rho_i\Big)\, \delta_k.$$
--
--   With all ratios equal to $1$ (the on-policy case) this reduces to the identity of Exercise 7.1 before termination.
--
--   **Formalization Note** The book poses this as Exercise 7.8 and gives no solution; the displayed weighted sum is the standard answer. The book uses (7.13) for $t < h < T$, i.e. before termination; the identity is algebraic and is stated for every $t \le h$ along a path, so termination does not enter. Where $b(A_i \mid S_i) = 0$, Lean's division gives $\rho_i = 0$, and the identity still holds.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 7.8, p. 151 (with (6.5), p. 121, and (7.13), p. 150)

import Mathlib
import Definitions.Def_SuttonBartoRL_NStep_EpisodeReturns

namespace SuttonBartoRL.NStep

/-- Sutton & Barto (2018), Exercise 7.8, p. 151: if the approximate state-value function `V` does
not change, the off-policy `n`-step return with control variate (7.13) is a sum of state-based TD
errors (6.5) weighted by products of importance sampling ratios:
`G_{t:h} − V(S_t) = Σ_{k=t}^{h−1} γ^{k−t} (Π_{i=t}^{k} ρ_i) δ_k`, for `t ≤ h`. -/
theorem controlVariateReturn_eq_sum_tdError {S A : Type} [Fintype A] (π b : Policy S A)
    (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (At : ℕ → A) (V : S → ℝ) (t h : ℕ) (hth : t ≤ h) :
    controlVariateReturn π b γ R St At V t h - V (St t) =
      ∑ k ∈ Finset.Ico t h,
        γ ^ (k - t) * (∏ i ∈ Finset.Icc t k, isRatio π b St At i) * tdError γ R St V k := by sorry

end SuttonBartoRL.NStep

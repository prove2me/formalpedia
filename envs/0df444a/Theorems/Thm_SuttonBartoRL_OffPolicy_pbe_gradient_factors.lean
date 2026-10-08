-- Prove2me | Theorems.Thm_SuttonBartoRL_OffPolicy_pbe_gradient_factors
-- name    : SuttonBartoRL.OffPolicy.pbe_gradient_factors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:02:25.509044+00:00
-- url     : https://prove2.me/theorems/f990d6de-b7ea-4d0e-83e8-78578ef06f2d
-- title:
--   The three factors of ∇PBE as expectations under the behavior policy (p. 278)
-- statement:
--   Let $\pi$ be the target and $b$ the behavior policy, with coverage ($\pi(a\mid s)>0\Rightarrow b(a\mid s)>0$) and ratio $\rho_t = \pi(A_t\mid S_t)/b(A_t\mid S_t)$. Let $S_t\sim\mu$ (the state distribution under $b$), $A_t\sim b(\cdot\mid S_t)$, $(S_{t+1},R_{t+1})\sim p(\cdot,\cdot\mid S_t,A_t)$, $\mathbf x_t = \mathbf x(S_t)$, $\mathbf x_{t+1} = \mathbf x(S_{t+1})$ and $\delta_t = R_{t+1} + \gamma\mathbf w^\top\mathbf x_{t+1} - \mathbf w^\top\mathbf x_t$. With $\mathbf D = \operatorname{diag}(\mu)$ and $P_\pi$ the target policy's transition matrix, for every $\mathbf w$:
--
--   1. $$\mathbf X^\top\mathbf D\bar\delta_{\mathbf w} = \sum_s\mu(s)\,\mathbf x(s)\,\bar\delta_{\mathbf w}(s) = \mathbb E[\rho_t\delta_t\mathbf x_t];$$
--   2. $$\mathbb E\bigl[\rho_t(\gamma\mathbf x_{t+1} - \mathbf x_t)\mathbf x_t^\top\bigr] = (\gamma P_\pi\mathbf X - \mathbf X)^\top\mathbf D\mathbf X;$$
--   3. $$\mathbf X^\top\mathbf D\mathbf X = \sum_s\mu(s)\,\mathbf x(s)\mathbf x(s)^\top = \mathbb E[\mathbf x_t\mathbf x_t^\top].$$
--
--   These identities turn the matrix form of the PBE gradient into the expectation form (11.27), whose factors can be sampled from off-policy experience.
--
--   **Formalization Note** Each expectation is written out as the finite sum over $s\sim\mu$, $a\sim b$ and $(s',r)\sim p$. Item 2 gives the value of the first factor of (11.27); the book obtains it as the transpose of the gradient of $\mathbb E[\rho_t\delta_t\mathbf x_t]$, and the goal theorem states that gradient in matrix form. $\mu$ need not be stationary for these identities.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §11.7, the three factor identities, p. 278

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_LinearGeometry

open Matrix

namespace SuttonBartoRL.OffPolicy

/-- Sutton & Barto (2018), p. 278: the three factors of the PBE gradient as expectations under the
behavior policy. Let `π` be the target and `b` the behavior policy with coverage
(`π(a|s) > 0 → b(a|s) > 0`), `ρ = π(a|s)/b(a|s)`, and `S_t ∼ µ`, `A_t ∼ b`,
`(S_{t+1}, R_{t+1}) ∼ p`, with `x_t = x(S_t)`, `x_{t+1} = x(S_{t+1})` and
`δ_t = R_{t+1} + γwᵀx_{t+1} − wᵀx_t`. Then
1. `XᵀDδ̄_w = Σ_s µ(s) x(s) δ̄_w(s) = E[ρ_t δ_t x_t]`;
2. `E[ρ_t (γx_{t+1} − x_t) x_tᵀ] = (γP_πX − X)ᵀ D X`;
3. `XᵀDX = Σ_s µ(s) x(s) x(s)ᵀ = E[x_t x_tᵀ]`. -/
theorem pbe_gradient_factors {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π b : SuttonBartoRL.FiniteMDP.Policy S A) (hcov : ∀ s a, 0 < π.prob s a → 0 < b.prob s a)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (μ : S → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (hμ1 : ∑ s, μ s = 1)
    (X : Matrix S (Fin d) ℝ) (w : Fin d → ℝ) :
    (Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X w) = ∑ s, (μ s * bellmanError M π γ X w s) • X s ∧
      ∑ s, (μ s * bellmanError M π γ X w s) • X s
        = behaviorExp M b μ
            (fun s a s' r => (isRatio π b s a * (r + γ * (w ⬝ᵥ X s') - w ⬝ᵥ X s)) • X s)) ∧
    behaviorExp M b μ (fun s a s' _ => isRatio π b s a • vecMulVec (γ • X s' - X s) (X s))
      = (γ • (policyTrans M π * X) - X)ᵀ * Dmat μ * X ∧
    (Xᵀ * Dmat μ * X = ∑ s, μ s • vecMulVec (X s) (X s) ∧
      ∑ s, μ s • vecMulVec (X s) (X s) = behaviorExp M b μ (fun s _ _ _ => vecMulVec (X s) (X s))) := by sorry

end SuttonBartoRL.OffPolicy

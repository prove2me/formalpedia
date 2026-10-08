-- Prove2me | Theorems.Thm_SuttonBartoRL_OffPolicy_pbe_gradient
-- name    : SuttonBartoRL.OffPolicy.pbe_gradient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:02:46.600053+00:00
-- url     : https://prove2.me/theorems/0002907d-f579-4def-899a-520ceee03af0
-- title:
--   (11.25)–(11.27) — the gradient of the projected Bellman error, matrix form
-- statement:
--   Let a finite MDP, a target policy $\pi$, a discount $\gamma\in[0,1]$, a state distribution $\mu$ with $\mathbf D = \operatorname{diag}(\mu)$, and a feature matrix $\mathbf X$ with $\mathbf X^\top\mathbf D\mathbf X$ invertible be given. Write $P_\pi$ for the policy's transition matrix and $\bar\delta_{\mathbf w} = B_\pi(\mathbf X\mathbf w) - \mathbf X\mathbf w$ for the Bellman error vector. Then at every $\mathbf w\in\mathbb R^d$:
--
--   1. $$\mathrm{PBE}(\mathbf w) = (\mathbf X^\top\mathbf D\bar\delta_{\mathbf w})^\top(\mathbf X^\top\mathbf D\mathbf X)^{-1}(\mathbf X^\top\mathbf D\bar\delta_{\mathbf w});$$
--   2. the PBE is differentiable at $\mathbf w$, with gradient
--   $$
--   \nabla\mathrm{PBE}(\mathbf w) = 2\,(\gamma P_\pi\mathbf X - \mathbf X)^\top\mathbf D\mathbf X\,(\mathbf X^\top\mathbf D\mathbf X)^{-1}\,\mathbf X^\top\mathbf D\bar\delta_{\mathbf w}.
--   $$
--
--   With $\mu$ the distribution of states visited under the behavior policy, the three factors are $\mathbb E[\rho_t(\gamma\mathbf x_{t+1}-\mathbf x_t)\mathbf x_t^\top]$, $\mathbb E[\mathbf x_t\mathbf x_t^\top]$ and $\mathbb E[\rho_t\delta_t\mathbf x_t]$ (p. 278), so item 2 is the book's (11.27),
--   $\nabla\mathrm{PBE}(\mathbf w) = 2\,\mathbb E[\rho_t(\gamma\mathbf x_{t+1}-\mathbf x_t)\mathbf x_t^\top]\,\mathbb E[\mathbf x_t\mathbf x_t^\top]^{-1}\,\mathbb E[\rho_t\delta_t\mathbf x_t]$. It is the expected update that the Gradient-TD methods GTD2 and TDC approximate.
--
--   **Formalization Note** The gradient is stated as a Fréchet derivative on $\mathbb R^d$ (`Fin d → ℝ`): the derivative is the linear map $\mathbf u\mapsto \mathbf g^\top\mathbf u$ with $\mathbf g$ the vector above. The matrix form is used because it involves no sampling; the expectation form follows from the milestone on the three factors. The pseudoinverse case of (11.13) is excluded by the invertibility hypothesis.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (11.25)–(11.27), pp. 278–279

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_LinearGeometry

open Matrix

namespace SuttonBartoRL.OffPolicy

/-- Sutton & Barto (2018), (11.25)–(11.27), pp. 278–279, in matrix form. For a finite MDP, a
policy `π`, `γ ∈ [0, 1]`, a state distribution `µ` with `D = diag(µ)`, and features `X` with `XᵀDX`
invertible, at every weight vector `w`:
1. `PBE(w) = (XᵀDδ̄_w)ᵀ (XᵀDX)⁻¹ (XᵀDδ̄_w)` (11.26);
2. `PBE` is (Fréchet) differentiable at `w`, and its derivative is `u ↦ g ⬝ u` with gradient
   `∇PBE(w) = g = 2 (γP_πX − X)ᵀ DX (XᵀDX)⁻¹ XᵀDδ̄_w`,
the matrix form of (11.27) (p. 278 identifies the three factors with
`E[ρ_t(γx_{t+1} − x_t)x_tᵀ]`, `E[x_tx_tᵀ]` and `E[ρ_tδ_tx_t]`). -/
theorem pbe_gradient {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (μ : S → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (hμ1 : ∑ s, μ s = 1)
    (X : Matrix S (Fin d) ℝ) (hX : IsUnit (Xᵀ * Dmat μ * X).det) (w : Fin d → ℝ) :
    PBE M π γ μ X w
        = (Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X w)) ⬝ᵥ
            ((Xᵀ * Dmat μ * X)⁻¹ *ᵥ (Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X w))) ∧
    ∃ L : (Fin d → ℝ) →L[ℝ] ℝ, HasFDerivAt (PBE M π γ μ X) L w ∧
      ∀ u : Fin d → ℝ,
        L u = ((2 : ℝ) • ((γ • (policyTrans M π * X) - X)ᵀ * Dmat μ * X * (Xᵀ * Dmat μ * X)⁻¹)
                *ᵥ (Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X w))) ⬝ᵥ u := by sorry

end SuttonBartoRL.OffPolicy

-- Prove2me | Theorems.Thm_SuttonBartoRL_OffPolicy_pbe_matrix_form
-- name    : SuttonBartoRL.OffPolicy.pbe_matrix_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:02:04.971863+00:00
-- url     : https://prove2.me/theorems/7bc8c59b-64ce-40c2-8342-cf757fd868cc
-- title:
--   (11.25)–(11.26) — the PBE in matrix terms
-- statement:
--   Let a finite MDP, a target policy $\pi$, a discount $\gamma\in[0,1]$, a state distribution $\mu$ with $\mathbf D = \operatorname{diag}(\mu)$, and a feature matrix $\mathbf X$ with $\mathbf X^\top\mathbf D\mathbf X$ invertible be given. For every weight vector $\mathbf w$, with $\bar\delta_{\mathbf w} = B_\pi v_{\mathbf w} - v_{\mathbf w}$ the Bellman error vector,
--   $$
--   \mathrm{PBE}(\mathbf w) = \|\Pi\bar\delta_{\mathbf w}\|_\mu^2
--   = \bar\delta_{\mathbf w}^\top\mathbf D\mathbf X(\mathbf X^\top\mathbf D\mathbf X)^{-1}\mathbf X^\top\mathbf D\bar\delta_{\mathbf w}
--   = (\mathbf X^\top\mathbf D\bar\delta_{\mathbf w})^\top(\mathbf X^\top\mathbf D\mathbf X)^{-1}(\mathbf X^\top\mathbf D\bar\delta_{\mathbf w}).
--   $$
--
--   This rewriting is the starting point of the Gradient-TD methods: it expresses the PBE through $d$-dimensional quantities that can be estimated from data.
--
--   **Formalization Note** The pseudoinverse case of (11.13) is excluded by the invertibility hypothesis. $\mu$ is only required to be a probability distribution (nonnegative, summing to one).
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (11.25)–(11.26), p. 278

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_LinearGeometry

open Matrix

namespace SuttonBartoRL.OffPolicy

/-- Sutton & Barto (2018), (11.25)–(11.26), p. 278: for a finite MDP, a policy `π`, `γ ∈ [0, 1]`, a
state distribution `µ` with `D = diag(µ)`, and features `X` with `XᵀDX` invertible, the projected
Bellman error of every weight vector `w` is
`PBE(w) = δ̄_wᵀ DX(XᵀDX)⁻¹XᵀD δ̄_w = (XᵀDδ̄_w)ᵀ (XᵀDX)⁻¹ (XᵀDδ̄_w)`. -/
theorem pbe_matrix_form {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (μ : S → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (hμ1 : ∑ s, μ s = 1)
    (X : Matrix S (Fin d) ℝ) (hX : IsUnit (Xᵀ * Dmat μ * X).det) (w : Fin d → ℝ) :
    PBE M π γ μ X w
        = bellmanError M π γ X w ⬝ᵥ
            ((Dmat μ * X * (Xᵀ * Dmat μ * X)⁻¹ * Xᵀ * Dmat μ) *ᵥ bellmanError M π γ X w) ∧
    PBE M π γ μ X w
        = (Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X w)) ⬝ᵥ
            ((Xᵀ * Dmat μ * X)⁻¹ *ᵥ (Xᵀ *ᵥ (Dmat μ *ᵥ bellmanError M π γ X w))) := by sorry

end SuttonBartoRL.OffPolicy

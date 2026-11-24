-- Prove2me | Theorems.Thm_SSLWithoutPairs_decoupled_dynamics
-- name    : SSLWithoutPairs.decoupled_dynamics
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:40:50.463807+00:00
-- url     : https://prove2.me/theorems/ca827921-a711-4933-8c98-61e081751d99
-- title:
--   Eqs. (11)-(13): decoupled dynamics of aligned eigenmodes
-- statement:
--   Let $\alpha_p>0$, $\eta\ge0$, and let $\tau(t)$ be continuous on $[0,\infty)$. Let $(F(t),W_p(t))$, $t\ge0$, solve the symmetrised dynamics (7). Suppose the eigenspaces are aligned at $t=0$: $W_p(0)=U\operatorname{diag}[p_1,\dots,p_d]U^\top$ and $F(0)=U\operatorname{diag}[s_1,\dots,s_d]U^\top$ for an orthogonal $U$. Then $U$ does not change: $W_p(t)=U\operatorname{diag}[p_j(t)]U^\top$ and $F(t)=U\operatorname{diag}[s_j(t)]U^\top$ for all $t\ge0$. Each mode obeys
--
--   $$\dot p_j=\alpha_ps_j[\tau-(1+\sigma^2)p_j]-\eta p_j,\qquad \dot s_j=2p_js_j[\tau-(1+\sigma^2)p_j]-2\eta s_j.$$
--
--   If in addition $F=WW^\top$ and the target network follows the EMA flow $\dot W_a=\beta(W-W_a)$, $\beta>0$, with $W_a(t)=\tau(t)W(t)$ (Assumption 1, $\tau$ differentiable), where $W(t)$ is differentiable, then each mode also satisfies
--
--   $$s_j\dot\tau=\beta(1-\tau)s_j-\tau\dot s_j/2.$$
--
--   **Formalization Note** Continuity of $\tau$ is added; in the paper $\tau$ is differentiable by Assumption 1. In the last equation, $\dot s_j$ is written as the right side of eq. (12).
-- source:
--   Tian, Chen and Ganguli, Understanding Self-Supervised Learning Dynamics without Contrastive Pairs, arXiv:2102.06810v4 (2021), Section 3.1, eqs. (11)-(13), p. 5; derivation in Appendix B.1, eqs. (76)-(91), pp. 17-19

import Mathlib
import Definitions.Def_SSLWithoutPairs_Basic

open MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace SSLWithoutPairs

theorem decoupled_dynamics {d : ℕ} (αp σ η : ℝ) (hαp : 0 < αp) (hη : 0 ≤ η) (τ : ℝ → ℝ)
    (hτ : ContinuousOn τ (Set.Ici 0)) (F Wp : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (hdWp : HasMatDerivOn Wp (fun t => symFlowWp αp σ η (τ t) (Wp t) (F t)))
    (hdF : HasMatDerivOn F (fun t => symFlowF σ η (τ t) (Wp t) (F t)))
    (U : Matrix.orthogonalGroup (Fin d) ℝ) (p₀ s₀ : Fin d → ℝ)
    (hWp0 : Wp 0 = (U : Matrix (Fin d) (Fin d) ℝ) * diagonal p₀ * (U : Matrix (Fin d) (Fin d) ℝ)ᵀ)
    (hF0 : F 0 = (U : Matrix (Fin d) (Fin d) ℝ) * diagonal s₀ * (U : Matrix (Fin d) (Fin d) ℝ)ᵀ) :
    ∃ p s : ℝ → Fin d → ℝ, p 0 = p₀ ∧ s 0 = s₀ ∧
      (∀ t : ℝ, 0 ≤ t →
        Wp t = (U : Matrix (Fin d) (Fin d) ℝ) * diagonal (p t) * (U : Matrix (Fin d) (Fin d) ℝ)ᵀ ∧
        F t = (U : Matrix (Fin d) (Fin d) ℝ) * diagonal (s t) * (U : Matrix (Fin d) (Fin d) ℝ)ᵀ) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ j,
        HasDerivWithinAt (fun r => p r j) (modeFlowP αp σ η (τ t) (p t j) (s t j)) (Set.Ici 0) t ∧
        HasDerivWithinAt (fun r => s r j) (modeFlowS σ η (τ t) (p t j) (s t j)) (Set.Ici 0) t) ∧
      (∀ (n₁ : ℕ) (β : ℝ) (W Wa W' : ℝ → Matrix (Fin d) (Fin n₁) ℝ) (τ' : ℝ → ℝ), 0 < β →
        (∀ t : ℝ, 0 ≤ t → F t = W t * (W t)ᵀ) → (∀ t : ℝ, 0 ≤ t → Wa t = τ t • W t) →
        HasMatDerivOn W W' → HasMatDerivOn Wa (fun t => β • (W t - Wa t)) →
        (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt τ (τ' t) (Set.Ici 0) t) →
        ∀ t : ℝ, 0 ≤ t → ∀ j, s t j * τ' t =
          β * (1 - τ t) * s t j - τ t * modeFlowS σ η (τ t) (p t j) (s t j) / 2) := by sorry

end SSLWithoutPairs

-- Prove2me | Theorems.Thm_SSLWithoutPairs_weight_decay_balancing
-- name    : SSLWithoutPairs.weight_decay_balancing
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:37:56.36116+00:00
-- url     : https://prove2.me/theorems/3ece3dbe-885c-43e5-974c-eebd83dff12b
-- title:
--   Theorem 1: weight decay promotes balancing of the predictor and online networks
-- statement:
--   Let $\alpha_p>0$, $\eta\ge0$, and let $X,X'$ be positive semidefinite $n_1\times n_1$ matrices. Let $W(t)\in\mathbb R^{n_2\times n_1}$ and $W_p(t)\in\mathbb R^{n_2\times n_2}$, $t\ge0$, solve
--
--   $$\dot W_p=\alpha_p\big(-W_pW(X+X')+W_aX\big)W^\top-\eta W_p,\qquad \dot W=W_p^\top\big(-W_pW(X+X')+W_aX\big)-\eta W,$$
--
--   where $W_a(t)$ is an arbitrary target trajectory (no dynamics for $W_a$ is assumed). Then, with the symmetric matrix $C=W(0)W(0)^\top-\alpha_p^{-1}W_p(0)^\top W_p(0)$, for all $t\ge0$
--
--   $$W(t)W(t)^\top=\alpha_p^{-1}W_p(t)^\top W_p(t)+e^{-2\eta t}C.$$
--
--   With weight decay, the memory of the initialization decays, so the online network and the predictor become balanced.
--
--   **Formalization Note** The paper says only that $C$ depends on the initialization. The statement gives its value, which is forced by setting $t=0$.
-- source:
--   Tian, Chen and Ganguli, Understanding Self-Supervised Learning Dynamics without Contrastive Pairs, arXiv:2102.06810v4 (2021), Section 2, Theorem 1, eq. (5), p. 3; proof in Appendix A, Theorem 1, eqs. (43)-(46), pp. 13-14

import Mathlib
import Definitions.Def_SSLWithoutPairs_Basic

open MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace SSLWithoutPairs

theorem weight_decay_balancing {n₁ n₂ : ℕ} (αp η : ℝ) (hαp : 0 < αp) (hη : 0 ≤ η)
    (X X' : Matrix (Fin n₁) (Fin n₁) ℝ) (hX : X.PosSemidef) (hX' : X'.PosSemidef)
    (Wp : ℝ → Matrix (Fin n₂) (Fin n₂) ℝ) (W Wa : ℝ → Matrix (Fin n₂) (Fin n₁) ℝ)
    (hWp : HasMatDerivOn Wp (fun t => byolFlowWp αp η X X' (Wp t) (W t) (Wa t)))
    (hW : HasMatDerivOn W (fun t => byolFlowW η X X' (Wp t) (W t) (Wa t))) :
    let C : Matrix (Fin n₂) (Fin n₂) ℝ := W 0 * (W 0)ᵀ - αp⁻¹ • ((Wp 0)ᵀ * Wp 0)
    Cᵀ = C ∧ ∀ t : ℝ, 0 ≤ t →
      W t * (W t)ᵀ = αp⁻¹ • ((Wp t)ᵀ * Wp t) + Real.exp (-2 * η * t) • C := by sorry

end SSLWithoutPairs

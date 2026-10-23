-- Prove2me | Theorems.Thm_RLInference_QValueCLT_covariance_identity
-- name    : RLInference.QValueCLT.covariance_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:13:08.127272+00:00
-- url     : https://prove2.me/theorems/5ce81e7b-a0b0-435b-9075-6af36c4bf235
-- title:
--   Proof of Theorem 1, p. 36, last display — ∇φ Σ_{R,P} ∇φᵀ = (I − γP̃^{π*})⁻¹W⁻¹[D_R + γ²D_Q]((I − γP̃^{π*})⁻¹)ᵀ
-- statement:
--   Let $Q=\operatorname{Fix}(\gamma,\mu_R,P)$, $V^*(k)=\max_aQ(k,a)$, let $a^*$ be any action map and $w>0$ any positive weight vector. Let
--
--   $$\nabla\phi=(I-\gamma\tilde P^{\pi^*})^{-1}\big[\,I\;\big|\;\gamma\operatorname{blockdiag}((V^*)^T,\dots,(V^*)^T)\,\big]$$
--
--   be the gradient of App. A.1, and $\Sigma_{R,P}=\operatorname{diag}(W^{-1}D_R,D_P)$ the covariance (8). Then
--
--   $$\nabla\phi\,\Sigma_{R,P}\,\nabla\phi^T=(I-\gamma\tilde P^{\pi^*})^{-1}W^{-1}\big[D_R+\gamma^2D_Q\big]\big((I-\gamma\tilde P^{\pi^*})^{-1}\big)^T,$$
--
--   which is the covariance $\Sigma$ of (5)–(6).
--
--   This identity turns the delta-method covariance into the closed form stated in Theorem 1.
--
--   **Formalization Note.** The identity is pure matrix algebra, with matrices indexed by $\mathcal S\times\mathcal A$ and $(\mathcal S\times\mathcal A)\times\mathcal S$. It does not use stationarity of $w$, the strict argmax, or $\gamma<1$; only $w>0$ is assumed, as in the paper.
-- source:
--   Zhu, Dong & Lam, Uncertainty Quantification and Exploration for Reinforcement Learning, arXiv:1910.05471v3, p. 36, App. A.1, last display; (5)–(6) p. 10, (8) p. 12

import Mathlib
import Definitions.Def_RLInference_QValueCLT_Setting
open MeasureTheory ProbabilityTheory Filter Matrix Topology

namespace RLInference.QValueCLT

theorem covariance_identity {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (γ : ℝ) (P : S × A → PMF S) (R : S × A → Measure ℝ) (aStar : S → A)
    (w : S × A → ℝ) (hw_pos : ∀ x, 0 < w x) :
    gradPhi γ (Pmat P) aStar (Vstar (bellmanFix γ (muR R) (Pmat P))) *
        SigmaRP (Pmat P) (sigma2R R) w *
        (gradPhi γ (Pmat P) aStar (Vstar (bellmanFix γ (muR R) (Pmat P))))ᵀ =
      SigmaQ γ (Pmat P) aStar (Vstar (bellmanFix γ (muR R) (Pmat P))) (sigma2R R) w := by sorry

end RLInference.QValueCLT

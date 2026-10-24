-- Prove2me | Theorems.Thm_SynDigits_Ridge_residual_split
-- name    : SynDigits.Ridge.residual_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:55.91619+00:00
-- url     : https://prove2.me/theorems/d8db9105-0130-4acb-b6f2-638206977cc3
-- title:
--   Appendix B.1, p. 32 — Ŷ_v − Y_v = Y(β̂ − β*) − r and ‖Ŷ_v − Y_v‖₂ ≤ ‖Y‖₂‖β̂ − β*‖₂ + ‖r‖₂
-- statement:
--   Let $n$ be the number of users, $m$ the number of existing questions and $d$ the latent dimension. The human responses to the existing questions form $Y \in \mathbb{R}^{n\times m}$, the digital-twin responses to the same questions form $\tilde Y \in \mathbb{R}^{n\times m}$, and the twin responses to the new question form $\tilde Y_v \in \mathbb{R}^n$. Write $\hat{\tilde\Sigma} = \frac1n \tilde Y^\top \tilde Y$ and $\hat{\tilde\gamma} = \frac1n \tilde Y^\top \tilde Y_v$ for the sample moments of the twin system, $\hat\beta = (\hat{\tilde\Sigma} + \lambda I)^{-1}\hat{\tilde\gamma}$ for the Ridge coefficients fitted on the twins with penalty $\lambda$, and $\hat Y_v = Y\hat\beta$ for the fit-and-transfer prediction of the human responses $Y_v \in \mathbb{R}^n$ to the new question. For a symmetric positive semidefinite $\tilde\Sigma \in \mathbb{R}^{m\times m}$ (the population second moment) and $\tilde\gamma \in \mathbb{R}^m$ (the population cross moment), let $\beta^* = (\tilde\Sigma + \lambda I)^{-1}\tilde\gamma$ and $r = Y_v - Y\beta^*$. Norms $\|\cdot\|_2$ of vectors are Euclidean, $\|\cdot\|_2$ of matrices is the spectral norm, and $\sigma_{\min}$ is the smallest singular value.
--
--   Then, by the definition of $r$,
--   $$\hat Y_v - Y_v = Y(\hat\beta - \beta^*) - r, \qquad \|\hat Y_v - Y_v\|_2 \le \|Y\|_2\,\|\hat\beta - \beta^*\|_2 + \|r\|_2 .$$
--
--   This is the first step of the proof of Theorem 4.1: it splits the prediction error into a coefficient-estimation part and the structural residual.
--
--   **Formalization Note** No hypotheses are needed: the identity and the bound hold for every value of the data, $\tilde\Sigma$, $\tilde\gamma$ and $\lambda$, whatever Lean's total inverse returns.
--
--   Differences from the source:
--   - generalization: Σ̃ = (1/n)𝔼[ỸᵀỸ] PSD, γ̃ = (1/n)𝔼[ỸᵀỸ_v], Ridge penalty λ ≥ 0 → any matrix Sig, any vector gam, any real lam (no hypothesis); reason: the step is an algebraic identity plus the triangle inequality and holds for every value, so it specializes to the paper's Σ̃, γ̃, λ
--   - reading: Ỹ ∈ ℝ^{n×(m+1)}; Σ̂̃, γ̂̃, β̂, Ŷ_v used but not defined → Yt = Ỹ_{1:m} : Matrix (Fin n) (Fin m) ℝ, ytv = Ỹ_v : Fin n → ℝ, sampleCov Yt = (1/n)ỸᵀỸ, sampleCross Yt ytv = (1/n)ỸᵀỸ_v, ridgeFit = (Σ̂̃+λI)⁻¹γ̂̃, ridgePredict = Y β̂; reason: Algorithm 1 fits Ỹ_{m+1} on Ỹ_{1:m}, and the m×m Σ̃ of p. 11 is the moment of Ỹ_{1:m}; the hat quantities are the sample analogues of the printed Σ̃, γ̃; the proof's normal equation (Σ̂̃+λI)β̂ = γ̂̃ (p. 32); Algorithm 1's Predict Ŷ_{m+1} = M(Y_{1:m}) (p. 6)
--   - encoding: vectors in ℝⁿ, n×m matrices, ‖·‖₂, spectral norm, σ_min → Fin n → ℝ, Matrix (Fin n) (Fin m) ℝ, vnorm, GaussianMatrix.specNorm, GaussianMatrix.sMin; reason: Lean representation of the same objects; same instances
-- source:
--   Fan, Huang, Peng, Wang, Wu, SYN-DIGITS: A Synthetic Control Framework for Calibrated Digital Twin Simulation, arXiv:2604.07513v1, p. 32, Appendix B.1, proof of Theorem 4.1, "By definition of r"

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SynDigits_Ridge_Model
open Matrix GaussianMatrix

namespace SynDigits.Ridge

theorem residual_split {n m : ℕ} (Y Yt : Matrix (Fin n) (Fin m) ℝ) (ytv Yv : Fin n → ℝ)
    (Sig : Matrix (Fin m) (Fin m) ℝ) (gam : Fin m → ℝ) (lam : ℝ) :
    ridgePredict Y Yt ytv lam - Yv
        = Y *ᵥ (ridgeFit Yt ytv lam - betaStar Sig gam lam) - resid Y Yv Sig gam lam ∧
      vnorm (ridgePredict Y Yt ytv lam - Yv)
        ≤ specNorm Y * vnorm (ridgeFit Yt ytv lam - betaStar Sig gam lam)
          + vnorm (resid Y Yv Sig gam lam) := by sorry

end SynDigits.Ridge

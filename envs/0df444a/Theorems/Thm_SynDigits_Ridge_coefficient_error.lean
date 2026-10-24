-- Prove2me | Theorems.Thm_SynDigits_Ridge_coefficient_error
-- name    : SynDigits.Ridge.coefficient_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:21.603794+00:00
-- url     : https://prove2.me/theorems/4194f11a-4e2b-4620-a27d-df593a6796bb
-- title:
--   Appendix B.1, p. 32 — normal equations and ‖β̂ − β*‖₂ ≤ (‖Σ̂̃ − Σ̃‖₂‖β*‖₂ + ‖γ̂̃ − γ̃‖₂)/(σ_min(Σ̂̃) + λ)
-- statement:
--   Let $n$ be the number of users, $m$ the number of existing questions and $d$ the latent dimension. The human responses to the existing questions form $Y \in \mathbb{R}^{n\times m}$, the digital-twin responses to the same questions form $\tilde Y \in \mathbb{R}^{n\times m}$, and the twin responses to the new question form $\tilde Y_v \in \mathbb{R}^n$. Write $\hat{\tilde\Sigma} = \frac1n \tilde Y^\top \tilde Y$ and $\hat{\tilde\gamma} = \frac1n \tilde Y^\top \tilde Y_v$ for the sample moments of the twin system, $\hat\beta = (\hat{\tilde\Sigma} + \lambda I)^{-1}\hat{\tilde\gamma}$ for the Ridge coefficients fitted on the twins with penalty $\lambda$, and $\hat Y_v = Y\hat\beta$ for the fit-and-transfer prediction of the human responses $Y_v \in \mathbb{R}^n$ to the new question. For a symmetric positive semidefinite $\tilde\Sigma \in \mathbb{R}^{m\times m}$ (the population second moment) and $\tilde\gamma \in \mathbb{R}^m$ (the population cross moment), let $\beta^* = (\tilde\Sigma + \lambda I)^{-1}\tilde\gamma$ and $r = Y_v - Y\beta^*$. Norms $\|\cdot\|_2$ of vectors are Euclidean, $\|\cdot\|_2$ of matrices is the spectral norm, and $\sigma_{\min}$ is the smallest singular value.
--
--   Assume $\sigma_{\min}(\hat{\tilde\Sigma}) + \lambda > 0$ and $\sigma_{\min}(\tilde\Sigma) + \lambda > 0$. Then:
--
--   1. $(\hat{\tilde\Sigma} + \lambda I)\hat\beta = \hat{\tilde\gamma}$ and $(\tilde\Sigma + \lambda I)\beta^* = \tilde\gamma$;
--   2. $(\hat{\tilde\Sigma} + \lambda I)(\hat\beta - \beta^*) = (\tilde\Sigma - \hat{\tilde\Sigma})\beta^* + (\hat{\tilde\gamma} - \tilde\gamma)$;
--   3. the coefficient error satisfies
--   $$\|\hat\beta - \beta^*\|_2 \le \frac{1}{\sigma_{\min}(\hat{\tilde\Sigma}) + \lambda}\Big(\|\hat{\tilde\Sigma} - \tilde\Sigma\|_2\,\|\beta^*\|_2 + \|\hat{\tilde\gamma} - \tilde\gamma\|_2\Big).$$
--
--   Combined with the residual split, this gives the first part of Theorem 4.1: the estimation error of the Ridge fit-and-transfer method.
--
--   **Formalization Note** The two positivity hypotheses make $\hat{\tilde\Sigma} + \lambda I$ and $\tilde\Sigma + \lambda I$ invertible, so $\hat\beta$ and $\beta^*$ are the genuine solutions of the normal equations rather than Lean's junk value $0$.
--
--   Differences from the source:
--   - generalization: Σ̃ = (1/n)𝔼[ỸᵀỸ], γ̃ = (1/n)𝔼[ỸᵀỸ_v] for a random twin matrix → any positive semidefinite Sig, any vector gam; reason: every such expectation is symmetric PSD, so the statement specializes to the paper's; the argument uses only (Σ̃+λI)β* = γ̃ and Σ̃ ⪰ 0
--   - generalization: Ridge penalty λ ≥ 0 → any real lam with the two positivity hypotheses; reason: the positivity hypotheses alone make both inverses genuine; λ ≥ 0 is a special case
--   - reading: Ỹ ∈ ℝ^{n×(m+1)}; Σ̂̃, γ̂̃, β̂, Ŷ_v used but not defined → Yt = Ỹ_{1:m} : Matrix (Fin n) (Fin m) ℝ, ytv = Ỹ_v : Fin n → ℝ, sampleCov Yt = (1/n)ỸᵀỸ, sampleCross Yt ytv = (1/n)ỸᵀỸ_v, ridgeFit = (Σ̂̃+λI)⁻¹γ̂̃, ridgePredict = Y β̂; reason: Algorithm 1 fits Ỹ_{m+1} on Ỹ_{1:m}, and the m×m Σ̃ of p. 11 is the moment of Ỹ_{1:m}; the hat quantities are the sample analogues of the printed Σ̃, γ̃; the proof's normal equation (Σ̂̃+λI)β̂ = γ̂̃ (p. 32); Algorithm 1's Predict Ŷ_{m+1} = M(Y_{1:m}) (p. 6)
--   - encoding: (Σ̂̃+λI)⁻¹ and (Σ̃+λI)⁻¹ exist (implicit) → 0 < sMin (sampleCov Yt) + lam and 0 < sMin Sig + lam; reason: for PSD S these exclude exactly the singular S + λI, where the paper's β̂, β* and the bound's denominators are undefined; Lean's inverse returns 0 there
--   - encoding: vectors in ℝⁿ, n×m matrices, ‖·‖₂, spectral norm, σ_min → Fin n → ℝ, Matrix (Fin n) (Fin m) ℝ, vnorm, GaussianMatrix.specNorm, GaussianMatrix.sMin; reason: Lean representation of the same objects; same instances
-- source:
--   Fan, Huang, Peng, Wang, Wu, SYN-DIGITS: A Synthetic Control Framework for Calibrated Digital Twin Simulation, arXiv:2604.07513v1, p. 32, Appendix B.1, proof of Theorem 4.1, "To bound ||β̂ − β*||₂"

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SynDigits_Ridge_Model
open Matrix GaussianMatrix

namespace SynDigits.Ridge

theorem coefficient_error {n m : ℕ} (Yt : Matrix (Fin n) (Fin m) ℝ) (ytv : Fin n → ℝ)
    (Sig : Matrix (Fin m) (Fin m) ℝ) (gam : Fin m → ℝ) (lam : ℝ)
    (hSig : Sig.PosSemidef)
    (hposHat : 0 < sMin (sampleCov Yt) + lam) (hpos : 0 < sMin Sig + lam) :
    (sampleCov Yt + lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ ridgeFit Yt ytv lam
        = sampleCross Yt ytv ∧
      (Sig + lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ betaStar Sig gam lam = gam ∧
      (sampleCov Yt + lam • (1 : Matrix (Fin m) (Fin m) ℝ))
          *ᵥ (ridgeFit Yt ytv lam - betaStar Sig gam lam)
        = (Sig - sampleCov Yt) *ᵥ betaStar Sig gam lam + (sampleCross Yt ytv - gam) ∧
      vnorm (ridgeFit Yt ytv lam - betaStar Sig gam lam)
        ≤ 1 / (sMin (sampleCov Yt) + lam)
          * (specNorm (sampleCov Yt - Sig) * vnorm (betaStar Sig gam lam)
            + vnorm (sampleCross Yt ytv - gam)) := by sorry

end SynDigits.Ridge

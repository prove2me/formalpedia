-- Prove2me | Theorems.Thm_SynDigits_Ridge_theorem_4_1
-- name    : SynDigits.Ridge.theorem_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:32.951966+00:00
-- url     : https://prove2.me/theorems/f17a9814-de23-4041-866b-a374a785ea9c
-- title:
--   Theorem 4.1, p. 11 — Ridge fit-and-transfer error on a new question: structural plus estimation error
-- statement:
--   **Setting (latent factor model, §4.1).** There are $n$ users, $m$ existing questions and a latent dimension $d$. User embeddings $U \in \mathbb{R}^{n\times d}$, question embeddings $V \in \mathbb{R}^{m\times d}$ (rows $v_j$) and a noise matrix $\mathcal E \in \mathbb{R}^{n\times m}$ give the human responses $Y = UV^\top + \mathcal E$. The new question has embedding $v \in \mathbb{R}^d$ and noise $\mathcal E_v \in \mathbb{R}^n$, and the (unobserved) human responses to it are $Y_v = Uv + \mathcal E_v$. Decompose $v = V^\top b + e$ with $b \in \mathbb{R}^m$ and $e \in \mathbb{R}^d$.
--
--   **Estimator (Ridge fit-and-transfer, §3.2).** The digital-twin responses are $\tilde Y \in \mathbb{R}^{n\times m}$ on the existing questions and $\tilde Y_v \in \mathbb{R}^n$ on the new one. With $\hat{\tilde\Sigma} = \frac1n\tilde Y^\top\tilde Y$, $\hat{\tilde\gamma} = \frac1n\tilde Y^\top\tilde Y_v$ and penalty $\lambda \ge 0$, the Ridge fit on the twins is $\hat\beta = (\hat{\tilde\Sigma} + \lambda I)^{-1}\hat{\tilde\gamma}$, and it is transferred to the humans as $\hat Y_v = Y\hat\beta$.
--
--   **Population target.** Let $\tilde\Sigma \in \mathbb{R}^{m\times m}$ be symmetric positive semidefinite and $\tilde\gamma \in \mathbb{R}^m$ (in the paper, $\tilde\Sigma = \frac1n\mathbb E[\tilde Y^\top\tilde Y]$ and $\tilde\gamma = \frac1n\mathbb E[\tilde Y^\top\tilde Y_v]$). Put $\beta^* = (\tilde\Sigma + \lambda I)^{-1}\tilde\gamma$ and $r = Y_v - Y\beta^*$. Assume $\sigma_{\min}(\hat{\tilde\Sigma}) + \lambda > 0$ and $\sigma_{\min}(\tilde\Sigma) + \lambda > 0$, where $\sigma_{\min}$ is the smallest singular value.
--
--   **Theorem.** With $\|\cdot\|_2$ the Euclidean norm on vectors and the spectral norm on matrices,
--   $$\|\hat Y_v - Y_v\|_2 \le \underbrace{\|r\|_2}_{\text{structural error}} + \underbrace{\frac{\|Y\|_2}{\sigma_{\min}(\hat{\tilde\Sigma}) + \lambda}\Big(\|\hat{\tilde\Sigma} - \tilde\Sigma\|_2\,\|\beta^*\|_2 + \|\hat{\tilde\gamma} - \tilde\gamma\|_2\Big)}_{\text{estimation error}},$$
--   with
--   $$\|r\|_2 \le \|Ue\|_2 + \|\mathcal E_v - \mathcal E b\|_2 + \frac{\|Y\|_2}{\sigma_{\min}(\tilde\Sigma) + \lambda}\Big(\lambda\|b\|_2 + \|\tilde\gamma - \tilde\Sigma b\|_2\Big).$$
--
--   The theorem explains why calibrating on digital-twin responses transfers to humans: the estimation error vanishes as the sample moments concentrate, and the structural error is small when the new question is nearly representable by existing ones and the twins' inter-question covariance is aligned with the humans'. Exact alignment of the two systems is not needed.
--
--   **Formalization Note** Both inequalities are conclusions (a conjunction). The two positivity hypotheses make $\hat{\tilde\Sigma} + \lambda I$ and $\tilde\Sigma + \lambda I$ invertible, so $\hat\beta$ and $\beta^*$ are not Lean's junk value $0$ and the denominators are positive. At $n = 0$ the factor $1/n$ is $0$ in Lean, but then $\hat Y_v - Y_v$ and $r$ live in $\mathbb R^0$, both left-hand sides are $0$, and the statement holds trivially.
--
--   Differences from the source:
--   - generalization: Σ̃ = (1/n)𝔼[ỸᵀỸ], γ̃ = (1/n)𝔼[ỸᵀỸ_v] for a random twin matrix → any positive semidefinite Sig, any vector gam; reason: every such expectation is symmetric PSD, so the statement specializes to the paper's; the argument uses only (Σ̃+λI)β* = γ̃ and Σ̃ ⪰ 0
--   - encoding: v = Vb + e → v = Vᵀ *ᵥ b + e; reason: V ∈ ℝ^{m×d} has the question embeddings as rows and b ∈ ℝ^m, so only Vᵀb type-checks; the proof's Yb = UVᵀb + ℰb (p. 32) confirms it
--   - reading: Y_v = Uv (§4.1, p. 9, noiseless); ℰ_v appears in Theorem 4.1 without a definition → hYv : Yv = U *ᵥ v + Ev; reason: Theorem 4.1 is stated "in the noisy setting" (p. 11) and its proof writes Y_v − Yb = Uv + ℰ_v − UVb − ℰb (p. 32), so Y_v = Uv + ℰ_v; Ev = 0 recovers the noiseless model of p. 9
--   - reading: Ỹ ∈ ℝ^{n×(m+1)}; Σ̂̃, γ̂̃, β̂, Ŷ_v used but not defined → Yt = Ỹ_{1:m} : Matrix (Fin n) (Fin m) ℝ, ytv = Ỹ_v : Fin n → ℝ, sampleCov Yt = (1/n)ỸᵀỸ, sampleCross Yt ytv = (1/n)ỸᵀỸ_v, ridgeFit = (Σ̂̃+λI)⁻¹γ̂̃, ridgePredict = Y β̂; reason: Algorithm 1 fits Ỹ_{m+1} on Ỹ_{1:m}, and the m×m Σ̃ of p. 11 is the moment of Ỹ_{1:m}; the hat quantities are the sample analogues of the printed Σ̃, γ̃; the proof's normal equation (Σ̂̃+λI)β̂ = γ̂̃ (p. 32); Algorithm 1's Predict Ŷ_{m+1} = M(Y_{1:m}) (p. 6)
--   - encoding: (Σ̂̃+λI)⁻¹ and (Σ̃+λI)⁻¹ exist (implicit) → 0 < sMin (sampleCov Yt) + lam and 0 < sMin Sig + lam; reason: for PSD S these exclude exactly the singular S + λI, where the paper's β̂, β* and the bound's denominators are undefined; Lean's inverse returns 0 there
--   - encoding: λ ≥ 0 (Ridge penalty, implicit) → 0 ≤ lam; reason: Ridge penalties are nonnegative; the printed λ‖b‖₂ equals ‖λb‖₂ only for λ ≥ 0
--   - encoding: vectors in ℝⁿ, n×m matrices, ‖·‖₂, spectral norm, σ_min → Fin n → ℝ, Matrix (Fin n) (Fin m) ℝ, vnorm, GaussianMatrix.specNorm, GaussianMatrix.sMin; reason: Lean representation of the same objects; same instances
-- source:
--   Fan, Huang, Peng, Wang, Wu, SYN-DIGITS: A Synthetic Control Framework for Calibrated Digital Twin Simulation, arXiv:2604.07513v1, p. 11, Theorem 4.1 (with the preamble on p. 11; setting §3.1–§3.2, pp. 5–6 and §4.1, p. 9; proof Appendix B.1, pp. 32–33)

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SynDigits_Ridge_Model
open Matrix GaussianMatrix

namespace SynDigits.Ridge

theorem theorem_4_1 {n m d : ℕ} (U : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin m) (Fin d) ℝ) (Eps Y : Matrix (Fin n) (Fin m) ℝ) (v e : Fin d → ℝ)
    (Ev Yv : Fin n → ℝ) (b : Fin m → ℝ) (Yt : Matrix (Fin n) (Fin m) ℝ) (ytv : Fin n → ℝ)
    (Sig : Matrix (Fin m) (Fin m) ℝ) (gam : Fin m → ℝ) (lam : ℝ)
    (hY : Y = U * Vᵀ + Eps) (hYv : Yv = U *ᵥ v + Ev) (hv : v = Vᵀ *ᵥ b + e)
    (hSig : Sig.PosSemidef) (hlam : 0 ≤ lam)
    (hposHat : 0 < sMin (sampleCov Yt) + lam) (hpos : 0 < sMin Sig + lam) :
    vnorm (ridgePredict Y Yt ytv lam - Yv)
        ≤ vnorm (resid Y Yv Sig gam lam)
          + specNorm Y / (sMin (sampleCov Yt) + lam)
            * (specNorm (sampleCov Yt - Sig) * vnorm (betaStar Sig gam lam)
              + vnorm (sampleCross Yt ytv - gam)) ∧
      vnorm (resid Y Yv Sig gam lam)
        ≤ vnorm (U *ᵥ e) + vnorm (Ev - Eps *ᵥ b)
          + specNorm Y / (sMin Sig + lam) * (lam * vnorm b + vnorm (gam - Sig *ᵥ b)) := by sorry

end SynDigits.Ridge

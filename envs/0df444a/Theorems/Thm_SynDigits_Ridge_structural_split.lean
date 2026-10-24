-- Prove2me | Theorems.Thm_SynDigits_Ridge_structural_split
-- name    : SynDigits.Ridge.structural_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:23.266376+00:00
-- url     : https://prove2.me/theorems/aaee3e3d-748b-4065-92f3-dfe4502927bd
-- title:
--   Appendix B.1, p. 33 — r = Ue + (ℰ_v − ℰb) + Y(b − β*) and ‖r‖₂ ≤ ‖Ue‖₂ + ‖ℰ_v − ℰb‖₂ + ‖Y‖₂‖b − β*‖₂
-- statement:
--   Consider the latent factor model of §4.1: there are user embeddings $U \in \mathbb{R}^{n\times d}$ and question embeddings $V \in \mathbb{R}^{m\times d}$ (rows $v_j$), a noise matrix $\mathcal E \in \mathbb{R}^{n\times m}$, and the human responses are $Y = UV^\top + \mathcal E$. The new question has embedding $v \in \mathbb{R}^d$ and noise $\mathcal E_v \in \mathbb{R}^n$, with human responses $Y_v = Uv + \mathcal E_v$. Decompose $v = V^\top b + e$ with coefficients $b \in \mathbb{R}^m$ and residual $e \in \mathbb{R}^d$. For any $\tilde\Sigma \in \mathbb{R}^{m\times m}$, $\tilde\gamma \in \mathbb{R}^m$ and $\lambda$, let $\beta^* = (\tilde\Sigma + \lambda I)^{-1}\tilde\gamma$ and $r = Y_v - Y\beta^*$. Then
--   $$r = Ue + (\mathcal E_v - \mathcal E b) + Y(b - \beta^*), \qquad \|r\|_2 \le \|Ue\|_2 + \|\mathcal E_v - \mathcal E b\|_2 + \|Y\|_2\,\|b - \beta^*\|_2 .$$
--
--   This splits the structural error of Theorem 4.1 into the part of the new question not representable by the existing ones, the noise, and the distance from $b$ to the population Ridge target.
--
--   **Formalization Note** The identity holds for any vector in place of $\beta^*$, so no invertibility hypothesis is needed here.
--
--   Differences from the source:
--   - generalization: Σ̃ = (1/n)𝔼[ỸᵀỸ] PSD, γ̃ = (1/n)𝔼[ỸᵀỸ_v], Ridge penalty λ ≥ 0 → any matrix Sig, any vector gam, any real lam (no hypothesis); reason: the step is an algebraic identity plus the triangle inequality and holds for every value, so it specializes to the paper's Σ̃, γ̃, λ
--   - encoding: v = Vb + e → v = Vᵀ *ᵥ b + e; reason: V ∈ ℝ^{m×d} has the question embeddings as rows and b ∈ ℝ^m, so only Vᵀb type-checks; the proof's Yb = UVᵀb + ℰb (p. 32) confirms it
--   - reading: Y_v = Uv (§4.1, p. 9, noiseless); ℰ_v appears in Theorem 4.1 without a definition → hYv : Yv = U *ᵥ v + Ev; reason: Theorem 4.1 is stated "in the noisy setting" (p. 11) and its proof writes Y_v − Yb = Uv + ℰ_v − UVb − ℰb (p. 32), so Y_v = Uv + ℰ_v; Ev = 0 recovers the noiseless model of p. 9
--   - encoding: vectors in ℝⁿ, n×m matrices, ‖·‖₂, spectral norm, σ_min → Fin n → ℝ, Matrix (Fin n) (Fin m) ℝ, vnorm, GaussianMatrix.specNorm, GaussianMatrix.sMin; reason: Lean representation of the same objects; same instances
-- source:
--   Fan, Huang, Peng, Wang, Wu, SYN-DIGITS: A Synthetic Control Framework for Calibrated Digital Twin Simulation, arXiv:2604.07513v1, p. 33, Appendix B.1, proof of Theorem 4.1, "So, r = …" (with the identity Y_v − Yb = Ue + ℰ_v − ℰb of p. 32)

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SynDigits_Ridge_Model
open Matrix GaussianMatrix

namespace SynDigits.Ridge

theorem structural_split {n m d : ℕ} (U : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin m) (Fin d) ℝ) (Eps Y : Matrix (Fin n) (Fin m) ℝ) (v e : Fin d → ℝ)
    (Ev Yv : Fin n → ℝ) (b : Fin m → ℝ) (Sig : Matrix (Fin m) (Fin m) ℝ) (gam : Fin m → ℝ)
    (lam : ℝ)
    (hY : Y = U * Vᵀ + Eps) (hYv : Yv = U *ᵥ v + Ev) (hv : v = Vᵀ *ᵥ b + e) :
    resid Y Yv Sig gam lam = U *ᵥ e + (Ev - Eps *ᵥ b) + Y *ᵥ (b - betaStar Sig gam lam) ∧
      vnorm (resid Y Yv Sig gam lam)
        ≤ vnorm (U *ᵥ e) + vnorm (Ev - Eps *ᵥ b)
          + specNorm Y * vnorm (b - betaStar Sig gam lam) := by sorry

end SynDigits.Ridge

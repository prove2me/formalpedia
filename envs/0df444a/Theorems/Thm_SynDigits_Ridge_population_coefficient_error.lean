-- Prove2me | Theorems.Thm_SynDigits_Ridge_population_coefficient_error
-- name    : SynDigits.Ridge.population_coefficient_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:30.457547+00:00
-- url     : https://prove2.me/theorems/fb1ea6eb-8370-468f-992a-85d36109ec79
-- title:
--   Appendix B.1, p. 33 — (Σ̃ + λI)(β* − b) = (γ̃ − Σ̃b) − λb and ‖β* − b‖₂ ≤ (‖γ̃ − Σ̃b‖₂ + λ‖b‖₂)/(σ_min(Σ̃) + λ)
-- statement:
--   Let $\tilde\Sigma \in \mathbb{R}^{m\times m}$ be symmetric positive semidefinite, $\tilde\gamma, b \in \mathbb{R}^m$, and $\lambda \ge 0$ with $\sigma_{\min}(\tilde\Sigma) + \lambda > 0$, where $\sigma_{\min}$ is the smallest singular value. Let $\beta^* = (\tilde\Sigma + \lambda I)^{-1}\tilde\gamma$. Then
--   $$(\tilde\Sigma + \lambda I)(\beta^* - b) = (\tilde\gamma - \tilde\Sigma b) - \lambda b$$
--   and
--   $$\|\beta^* - b\|_2 \le \frac{1}{\sigma_{\min}(\tilde\Sigma) + \lambda}\Big(\|\tilde\gamma - \tilde\Sigma b\|_2 + \lambda\|b\|_2\Big).$$
--
--   Combined with the structural split, this yields the second part of Theorem 4.1, the bound on the structural error $\|r\|_2$.
--
--   **Formalization Note** The hypothesis $\sigma_{\min}(\tilde\Sigma) + \lambda > 0$ makes $\tilde\Sigma + \lambda I$ invertible, so $\beta^*$ is the genuine solution of $(\tilde\Sigma + \lambda I)\beta^* = \tilde\gamma$ rather than Lean's junk value $0$.
--
--   Differences from the source:
--   - generalization: Σ̃ = (1/n)𝔼[ỸᵀỸ], γ̃ = (1/n)𝔼[ỸᵀỸ_v] for a random twin matrix → any positive semidefinite Sig, any vector gam; reason: every such expectation is symmetric PSD, so the statement specializes to the paper's; the argument uses only (Σ̃+λI)β* = γ̃ and Σ̃ ⪰ 0
--   - encoding: (Σ̃+λI)⁻¹ exists (implicit) → 0 < sMin Sig + lam; reason: for PSD Σ̃ this excludes exactly the singular Σ̃ + λI, where the paper's β* and the bound's denominator are undefined; Lean's inverse returns 0 there
--   - encoding: λ ≥ 0 (Ridge penalty, implicit) → 0 ≤ lam; reason: Ridge penalties are nonnegative; the printed λ‖b‖₂ equals ‖λb‖₂ only for λ ≥ 0
--   - encoding: vectors in ℝⁿ, n×m matrices, ‖·‖₂, spectral norm, σ_min → Fin n → ℝ, Matrix (Fin n) (Fin m) ℝ, vnorm, GaussianMatrix.specNorm, GaussianMatrix.sMin; reason: Lean representation of the same objects; same instances
-- source:
--   Fan, Huang, Peng, Wang, Wu, SYN-DIGITS: A Synthetic Control Framework for Calibrated Digital Twin Simulation, arXiv:2604.07513v1, p. 33, Appendix B.1, proof of Theorem 4.1, "To bound ||b − β*||₂"

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SynDigits_Ridge_Model
open Matrix GaussianMatrix

namespace SynDigits.Ridge

theorem population_coefficient_error {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ)
    (gam b : Fin m → ℝ) (lam : ℝ)
    (hSig : Sig.PosSemidef) (hlam : 0 ≤ lam) (hpos : 0 < sMin Sig + lam) :
    (Sig + lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ (betaStar Sig gam lam - b)
        = (gam - Sig *ᵥ b) - lam • b ∧
      vnorm (betaStar Sig gam lam - b)
        ≤ 1 / (sMin Sig + lam) * (vnorm (gam - Sig *ᵥ b) + lam * vnorm b) := by sorry

end SynDigits.Ridge

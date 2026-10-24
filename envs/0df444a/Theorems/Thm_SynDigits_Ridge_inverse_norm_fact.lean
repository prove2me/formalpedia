-- Prove2me | Theorems.Thm_SynDigits_Ridge_inverse_norm_fact
-- name    : SynDigits.Ridge.inverse_norm_fact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:13.298595+00:00
-- url     : https://prove2.me/theorems/447a713e-b21d-4822-8d1b-a62a2adad977
-- title:
--   Appendix B.1, p. 32 — ‖(S + λI)⁻¹‖₂⁻¹ = σ_min(S) + λ for positive semidefinite S
-- statement:
--   Let $m \ge 1$, let $S \in \mathbb{R}^{m\times m}$ be symmetric positive semidefinite, and let $\lambda \in \mathbb{R}$ with $\sigma_{\min}(S) + \lambda > 0$, where $\sigma_{\min}$ is the smallest singular value. Then $S + \lambda I$ is invertible and
--   $$\big\|(S + \lambda I)^{-1}\big\|_2^{-1} = \sigma_{\min}(S) + \lambda ,$$
--   where $\|\cdot\|_2$ is the spectral norm.
--
--   The proof of Theorem 4.1 uses this fact twice: for the sample second moment $\hat{\tilde\Sigma}$ (p. 32) and for the population second moment $\tilde\Sigma$ (p. 33). It turns the norm of the regularized inverse into the denominators of both error bounds.
--
--   **Formalization Note** $\sigma_{\min}(S)$ is `GaussianMatrix.sMin S`, the infimum of $\|Sx\|_2$ over unit vectors $x$; for positive semidefinite $S$ it is the smallest eigenvalue.
--
--   Differences from the source:
--   - generalization: the fact for S = Σ̂̃ (p. 32) and S = Σ̃ (p. 33) with Ridge penalty λ ≥ 0 → every PSD S and every real lam with 0 < sMin S + lam; reason: both instances are PSD with λ ≥ 0, so the statement specializes to each use in the proof
--   - encoding: (S + λI)⁻¹ exists (implicit) → 0 < sMin S + lam; reason: for PSD S this excludes exactly the singular S + λI; Lean's inverse returns 0 there
--   - encoding: matrices of size m×m with m ≥ 1 (implicit) → 0 < m; reason: for m = 0 the empty matrix has spectral norm 0 and sMin is 0 by convention, so the identity would read 0 = λ; the paper's matrices are nonempty
--   - encoding: vectors in ℝⁿ, n×m matrices, ‖·‖₂, spectral norm, σ_min → Fin n → ℝ, Matrix (Fin n) (Fin m) ℝ, vnorm, GaussianMatrix.specNorm, GaussianMatrix.sMin; reason: Lean representation of the same objects; same instances
-- source:
--   Fan, Huang, Peng, Wang, Wu, SYN-DIGITS: A Synthetic Control Framework for Calibrated Digital Twin Simulation, arXiv:2604.07513v1, p. 32, Appendix B.1, proof of Theorem 4.1, "where we used the fact that" (used again on p. 33)

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SynDigits_Ridge_Model
open Matrix GaussianMatrix

namespace SynDigits.Ridge

theorem inverse_norm_fact {m : ℕ} (hm : 0 < m) (S : Matrix (Fin m) (Fin m) ℝ)
    (hS : S.PosSemidef) (lam : ℝ) (hpos : 0 < sMin S + lam) :
    (specNorm (S + lam • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹)⁻¹ = sMin S + lam := by sorry

end SynDigits.Ridge

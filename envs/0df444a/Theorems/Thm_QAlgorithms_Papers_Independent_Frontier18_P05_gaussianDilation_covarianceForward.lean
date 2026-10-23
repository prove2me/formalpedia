-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P05_gaussianDilation_covarianceForward
-- name    : QAlgorithms.Papers.Independent.Frontier18.P05.gaussianDilation_covarianceForward
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:45:49.709994+00:00
-- url     : https://prove2.me/theorems/a8ee58f8-bdc0-4090-8b0a-5f121983171d
-- title:
--   Gaussian dilation induces a completely positive covariance map
-- statement:
--   Let $n\ge1$ and $q\ge0$ be the system and environment mode numbers. Write $\sigma_n=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$ and let $\omega_E$ be the canonical $q$-mode commutation matrix with any permutation of its coordinates. Let $G$ be real symmetric with $G-i\omega_E\succeq0$. Suppose the real block matrix $S=\begin{pmatrix}s_1&s_2\\s_3&s_4\end{pmatrix}$ preserves $\sigma_n\oplus\omega_E$. Then $X=s_1^T$ and $Y=s_2Gs_2^T$ satisfy $Y=Y^T\succeq0$ and
--
--   $$Y-i(\sigma_n-X^T\sigma_nX)\succeq0.$$
--
--   For every physical system covariance $\gamma$, the system block of $S(\gamma\oplus G)S^T$ equals $X^T\gamma X+Y$. This identifies the covariance map induced by a Gaussian symplectic coupling.
-- source:
--   Multi-mode bosonic Gaussian channels, arXiv:0804.0511v3, PDF p. 8, Proposition 1: Unitary dilations of Gaussian channels

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P05

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P05

open QAlgorithms.Papers.Independent.Dependency50.P10

/-- Proposition 1, PDF p.8, Eqs.(23)–(24). CP is concluded, not assumed.
The covariance identity ranges over all physical input covariances. -/
theorem gaussianDilation_covarianceForward {n q : ℕ} (hn : 0 < n)
    (omega G : Matrix (Phase q) (Phase q) ℝ)
    (hOmega : IsEnvironmentalForm omega) (hG : physicalCovariance G omega)
    (s1 : Matrix (Phase n) (Phase n) ℝ)
    (s2 : Matrix (Phase n) (Phase q) ℝ)
    (s3 : Matrix (Phase q) (Phase n) ℝ)
    (s4 : Matrix (Phase q) (Phase q) ℝ)
    (hS : let S := Matrix.fromBlocks s1 s2 s3 s4
          let form := Matrix.fromBlocks (sigma n) 0 0 omega
          S * form * S.transpose = form) :
    ∃ X Y : Matrix (Phase n) (Phase n) ℝ,
      X = s1.transpose ∧ Y = s2 * G * s2.transpose ∧
      Y.transpose = Y ∧ Y.PosSemidef ∧ (cpMatrix X Y).PosSemidef ∧
      ∀ gamma : Matrix (Phase n) (Phase n) ℝ,
        physicalCovariance gamma (sigma n) →
        (let S := Matrix.fromBlocks s1 s2 s3 s4
         (S * Matrix.fromBlocks gamma 0 0 G * S.transpose).toBlocks₁₁ =
           X.transpose * gamma * X + Y) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P05

end

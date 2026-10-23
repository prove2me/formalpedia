-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P05_gaussianDilation_covarianceConverse
-- name    : QAlgorithms.Papers.Independent.Frontier18.P05.gaussianDilation_covarianceConverse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:47:12.551351+00:00
-- url     : https://prove2.me/theorems/55d6512e-4544-46bb-ab29-09e116b39097
-- title:
--   Every Gaussian CP pair admits a symplectic covariance dilation
-- statement:
--   Let $n\ge1$, let $X,Y$ be real $2n\times2n$ matrices, and put $\Sigma=\sigma_n-X^T\sigma_nX$, where $\sigma_n=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$. If $Y-i\Sigma\succeq0$, there exist an integer $q\le2n$, a physical $q$-mode covariance $G$, and real blocks $s_2,s_3,s_4$ such that
--
--   $$s_2\sigma_qs_2^T=\Sigma,\qquad s_2Gs_2^T=Y,\qquad S(\sigma_n\oplus\sigma_q)S^T=\sigma_n\oplus\sigma_q,$$
--
--   where $S=\begin{pmatrix}X^T&s_2\\s_3&s_4\end{pmatrix}$. For every physical input covariance $\gamma$, the system block of $S(\gamma\oplus G)S^T$ is $X^T\gamma X+Y$. The same environment and coupling work for every such $\gamma$, including singular-noise cases. This is the numbered covariance theorem; the full all-input channel theorem is a separate node.
-- source:
--   Multi-mode bosonic Gaussian channels, arXiv:0804.0511v3, PDF p. 9, Theorem 1: Unitary dilations, converse implication

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P05

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P05

open QAlgorithms.Papers.Independent.Dependency50.P10

/-- Theorem 1, PDF p.9, proof through p.13, Eqs.(24)–(26). This is the numbered
covariance theorem, with both coupling identities. Singular X,Y,Sigma are allowed.
The environment is chosen before the universally quantified input covariance. -/
theorem gaussianDilation_covarianceConverse {n : ℕ} (hn : 0 < n)
    (X Y : Matrix (Phase n) (Phase n) ℝ) (hCP : (cpMatrix X Y).PosSemidef) :
    ∃ q : ℕ, q ≤ 2 * n ∧
      ∃ G : Matrix (Phase q) (Phase q) ℝ,
        ∃ s2 : Matrix (Phase n) (Phase q) ℝ,
          ∃ s3 : Matrix (Phase q) (Phase n) ℝ,
            ∃ s4 : Matrix (Phase q) (Phase q) ℝ,
              physicalCovariance G (sigma q) ∧
              s2 * sigma q * s2.transpose = commutatorDefect X ∧
              s2 * G * s2.transpose = Y ∧
              (let S := Matrix.fromBlocks X.transpose s2 s3 s4
               S * jointSigma n q * S.transpose = jointSigma n q) ∧
              ∀ gamma : Matrix (Phase n) (Phase n) ℝ,
                physicalCovariance gamma (sigma n) →
                (let S := Matrix.fromBlocks X.transpose s2 s3 s4
                 (S * Matrix.fromBlocks gamma 0 0 G * S.transpose).toBlocks₁₁ =
                   X.transpose * gamma * X + Y) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P05

end

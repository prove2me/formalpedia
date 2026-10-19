-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P05_symplecticRows_completion
-- name    : QAlgorithms.Papers.Independent.Frontier18.P05.symplecticRows_completion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:46:29.953082+00:00
-- url     : https://prove2.me/theorems/7dff9d9e-bef1-4939-8b63-69d04ec7670b
-- title:
--   Completion of symplectic rows
-- statement:
--   Let $n\ge1$, $q\ge0$, and let $\omega_E$ be an actual canonical $q$-mode commutation form, possibly with reordered coordinates. Given real matrices $s_1\in\mathbb R^{2n\times2n}$ and $s_2\in\mathbb R^{2n\times2q}$ satisfying
--
--   $$s_1\sigma_ns_1^T+s_2\omega_Es_2^T=\sigma_n,$$
--
--   there exist real blocks $s_3,s_4$ such that $S=\begin{pmatrix}s_1&s_2\\s_3&s_4\end{pmatrix}$ satisfies $S(\sigma_n\oplus\omega_E)S^T=\sigma_n\oplus\omega_E$. Here $\sigma_n=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$. This completion preserves the prescribed top rows and supplies the remaining dilation blocks.
-- source:
--   Multi-mode bosonic Gaussian channels, arXiv:0804.0511v3, PDF p. 9, Lemma 1: Extensions of symplectic forms

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P05

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P05

open QAlgorithms.Papers.Independent.Dependency50.P10

/-- Lemma 1, PDF p.9; Appendix A, PDF pp.29–30. The environmental form
is nondegenerate as required by Eq.(21). The prescribed top rows are retained. -/
theorem symplecticRows_completion {n q : ℕ} (hn : 0 < n)
    (omega : Matrix (Phase q) (Phase q) ℝ)
    (hOmega : IsEnvironmentalForm omega)
    (s1 : Matrix (Phase n) (Phase n) ℝ)
    (s2 : Matrix (Phase n) (Phase q) ℝ)
    (hRows : s1 * sigma n * s1.transpose + s2 * omega * s2.transpose = sigma n) :
    ∃ s3 : Matrix (Phase q) (Phase n) ℝ,
      ∃ s4 : Matrix (Phase q) (Phase q) ℝ,
        let S := Matrix.fromBlocks s1 s2 s3 s4
        let form := Matrix.fromBlocks (sigma n) 0 0 omega
        S * form * S.transpose = form := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P05

end

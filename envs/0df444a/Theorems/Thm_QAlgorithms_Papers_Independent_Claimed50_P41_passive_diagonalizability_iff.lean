-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_passive_diagonalizability_iff
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.passive_diagonalizability_iff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:08:32.643634+00:00
-- url     : https://prove2.me/theorems/faa3dd0a-d279-4f74-a339-f52f57bf66cc
-- title:
--   §XI (11.2)–(11.3): passive diagonalizability iff AB symmetric
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. For a real symmetric covariance matrix $V$, put $V^{(c)}=\Omega V\Omega^\dagger=\begin{pmatrix}A&B\\\overline B&\overline A\end{pmatrix}$, where $\Omega=2^{-1/2}\begin{pmatrix}I&iI\\I&-iI\end{pmatrix}$. Let $\mathcal S=\{V>0:V+i\beta/2\succeq0\}$. Vacuum has covariance $I/2$. Let V belong to S.
--
--   $$
--   \exists K_0\in K:\ K_0VK_0^T\text{ diagonal}\iff AB=(AB)^T.
--   $$
--
--   For K(U0) with U0 unitary, the complex blocks transform as A to U0 A U0 dagger and B to U0 B U0 transpose. Both directions of the characterization are retained.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 34, §XI (11.2)–(11.3): passive diagonalizability iff AB symmetric

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.33–34, (11.2)–(11.3): passive diagonalizability iff AB is
symmetric, together with the separate A,B transformation laws. -/
theorem passive_diagonalizability_iff (n : ℕ) (hn : 0 < n)
    (V : Matrix (Phase n) (Phase n) ℝ) (hV : Allowed V) :
    ((∃ K : Matrix (Phase n) (Phase n) ℝ, IsPassive K ∧ IsDiagonal (K * V * K.transpose)) ↔
      (noiseA V * noiseB V).IsSymm) ∧
    (∀ X Y : Matrix (Fin n) (Fin n) ℝ, IsPassive (passiveMatrix X Y) →
      let K := passiveMatrix X Y
      let U := unitaryParameter X Y
      noiseA (K * V * K.transpose) = U * noiseA V * U.conjTranspose ∧
      noiseB (K * V * K.transpose) = U * noiseB V * U.transpose) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end

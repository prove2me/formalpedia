-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P27_coherence_score_identity
-- name    : QAlgorithms.Papers.Independent.Information100.P27.coherence_score_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:16:42.159425+00:00
-- url     : https://prove2.me/theorems/d3ee0b68-d362-4316-b5bc-786052b3f960
-- title:
--   §8.2.4: matrix score as a weighted coherence difference
-- statement:
--   Let $r$ be a density matrix on a positive finite dimension in its distinguished basis, with $p_i=r_{ii}>0$, and set $G_{ij}=r_{ij}/\sqrt{p_ip_j}$. For a density matrix $\theta$, write $\Delta(\theta)$ for complete basis dephasing, $N_G(\theta)=G\circ\theta$ for the Schur channel, and $C_r(\theta)=H(\Delta(\theta))-H(\theta)$ for relative entropy of coherence. For $\mu\ge0$, define $L^G_\mu(\theta)=H(\Delta(\theta))+\mu H(\theta)-(1+\mu)H(N_G(\theta))$. Then
--
--   $$
--   (1+\mu)C_r(N_G(\theta))-\mu C_r(\theta)=L^G_\mu(\theta).
--   $$
--
--   All entropies are in bits. This identity rewrites the matrix objective without asserting additivity of its weighted difference.
-- source:
--   Static classical-quantum- entanglement trade-offs: an entropic converse and single-letter characterizations, arXiv:2609.23298v1, PDF p. 36, §8.2.4: matrix score as a weighted coherence difference

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P27

/-- arXiv:2609.23298v1 PDF p.36, (8.36)-(8.37): weighted coherence identity. -/
theorem coherence_score_identity {d : ℕ} (hd : 0 < d)
    (r theta : Matrix (Fin d) (Fin d) ℂ) (hr : IsDensityMatrix r)
    (hp : ∀ i, 0 < (r i i).re) (htheta : IsDensityMatrix theta)
    (mu : ℝ) (hmu : 0 ≤ mu) :
    (1 + mu) * coherence (schur (correlation r) theta) - mu * coherence theta =
      matrixScore mu (correlation r) theta := by sorry

end QAlgorithms.Papers.Independent.Information100.P27

end

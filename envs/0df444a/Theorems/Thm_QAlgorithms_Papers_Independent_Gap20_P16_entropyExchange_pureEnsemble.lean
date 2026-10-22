-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P16_entropyExchange_pureEnsemble
-- name    : QAlgorithms.Papers.Independent.Gap20.P16.entropyExchange_pureEnsemble
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:40:32.133277+00:00
-- url     : https://prove2.me/theorems/f82e591a-f949-4c3a-b87e-0b4a32d11133
-- title:
--   Entropy exchange bounds the average pure-input output entropy
-- statement:
--   Let $d\ge1$ and let $\Phi$ be a completely positive trace-preserving map on the complex $d\times d$ matrices. Let $\{(p_j,\psi_j)\}_{j=1}^m$ be any finite ensemble with $p_j\ge0$, $\sum_jp_j=1$, and $\|\psi_j\|=1$. Set $\rho_j=|\psi_j\rangle\langle\psi_j|$ and $\rho=\sum_jp_j\rho_j$. Then
--
--   $$
--   H(\rho,\Phi)\ge\sum_jp_jH(\Phi(\rho_j)).
--   $$
--
--   Here $H$ is entropy in bits and $H(\rho,\Phi)$ is the entropy of the joint reference–output state after applying $\Phi$ to a purification of $\rho$. Zero ensemble weights are allowed. This independent entropy inequality supplies the capacity comparison in section 2.
-- source:
--   Remarks on the classical capacity of quantum channel, arXiv:quant-ph/0212025v1, PDF p. 4, §2, (13); proof p.5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P16

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

/-- PDF pp.4--5, (13): entropy exchange dominates the average output
entropy of every finite ensemble of normalized pure inputs, including zero
weights. The average state is computed, not assumed as unrelated data.
The accepted canonical-purification entropy exchange uses a pure reference
and is independent of the choice of a pure Stinespring environment. -/
theorem entropyExchange_pureEnsemble
    {d : ℕ} (hd : 0 < d) (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (e : QAlgorithms.Papers.Independent.Information100.P08.PureEnsemble (Fin d)) :
    ∑ j, e.prob j * vnEntropy (Phi (pureDensity (e.vector j))) ≤
      QAlgorithms.Papers.Independent.Dependency50.P45.entropyExchange Phi
        (QAlgorithms.Papers.Independent.Information100.P08.pureAverage e) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P16

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P25_quadratic_holevo_pair_distance
-- name    : QAlgorithms.Papers.Independent.Advance50.P25.quadratic_holevo_pair_distance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:54:26.402394+00:00
-- url     : https://prove2.me/theorems/da3b2875-f48e-449e-9a62-71fe59da6895
-- title:
--   Quadratic Holevo quantity equals a pair-distance sum
-- statement:
--   Let $\{p_j,\rho_j\}_{j=0}^{m-1}$ be a finite ensemble of density operators on one finite-dimensional complex system, with $p_j\ge0$ and $\sum_jp_j=1$. Its component states may be mixed. Set $\bar\rho=\sum_jp_j\rho_j$, $S_Q(\rho)=1-\operatorname{Tr}(\rho^2)$, and $D_{\mathrm{HS}}(\rho,\sigma)=\operatorname{Tr}[(\rho-\sigma)^2]$. Then
--
--   $$
--   \chi_Q(\{p_j,\rho_j\})
--   =S_Q(\bar\rho)-\sum_jp_jS_Q(\rho_j)
--   =\sum_{0\le j<k<m}p_jp_kD_{\mathrm{HS}}(\rho_j,\rho_k).
--   $$
--
--   Every unordered distinct pair is counted once. The average state is computed from the ensemble, and deterministic ensembles and zero weights are allowed.
--
--   This exact identity relates the quadratic Holevo quantity to Hilbert–Schmidt distances.
-- source:
--   Non-negative discord strengthens the subadditivity of quantum entropy functions, arXiv:1101.1717v1, PDF p. 4, §V, Eq.(25): exact quadratic Holevo pair-distance identity

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P25

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)

open QAlgorithms.Papers.Independent.Claimed50.P48 (nonzeroSpectrum)

open QAlgorithms.Papers.Independent.Gap48.P33 (discardLast)

/-- PDF p.4, Eq.(25): one term per unordered distinct pair; components may be mixed. -/
theorem quadratic_holevo_pair_distance {I : Type}
    [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (p : Fin m → ℝ) (rho : Fin m → Matrix I I ℂ) (hens : DensityEnsemble p rho) :
    generalEntropyHolevo quadraticEntropy p rho =
      ∑ j : Fin m, ∑ k : Fin m with j < k,
        p j * p k * hilbertSchmidtDistance (rho j) (rho k) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P25

end

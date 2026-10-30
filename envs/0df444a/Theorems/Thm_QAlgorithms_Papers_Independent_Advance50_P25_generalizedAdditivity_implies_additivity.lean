-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P25_generalizedAdditivity_implies_additivity
-- name    : QAlgorithms.Papers.Independent.Advance50.P25.generalizedAdditivity_implies_additivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:56:30.547853+00:00
-- url     : https://prove2.me/theorems/8c505e2f-5237-44f6-8d89-dfb39dade628
-- title:
--   Generalized additivity implies product additivity
-- statement:
--   Let $S_K$ be a concave spectral entropy family on finite-dimensional complex density operators, invariant under zero padding and zero on pure states. Suppose it satisfies the following generalized additivity rule for all finite positive dimensions, orthonormal bases $\{|w_j\rangle\}$, probability distributions $p_j$, and density operators $\rho_{bj}$:
--
--   $$
--   S_K\!\left(\sum_jp_j|w_j\rangle\langle w_j|\otimes\rho_{bj}\right)
--   =S_K(\rho_a)+\sum_jp_jS_K(\rho_{bj}),
--   $$
--
--   where $\rho_a$ is the actual first marginal of the displayed cq density. Then, for every pair of density operators $\rho_a,\rho_b$,
--
--   $$
--   S_K(\rho_a\otimes\rho_b)=S_K(\rho_a)+S_K(\rho_b).
--   $$
--
--   Spectral invariance makes a single basis per dimension equivalent to every basis. The hypothesis is a global entropy property, and therefore strengthens ordinary product additivity.
-- source:
--   Non-negative discord strengthens the subadditivity of quantum entropy functions, arXiv:1101.1717v1, PDF p. 4, Proposition 6 (§VII): generalized additivity implies additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P25

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)

open QAlgorithms.Papers.Independent.Claimed50.P48 (nonzeroSpectrum)

open QAlgorithms.Papers.Independent.Gap48.P33 (discardLast)

/-- PDF pp.4–5, Proposition 6: the cq chain rule globally implies product additivity. -/
theorem generalizedAdditivity_implies_additivity (S : EntropyFunction) (hS : IsEntropy S) :
    GeneralizedAdditive S → AdditiveEntropy S := by sorry

end QAlgorithms.Papers.Independent.Advance50.P25

end

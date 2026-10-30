-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P25_cq_chain_rule_iff_zero_basis_discord
-- name    : QAlgorithms.Papers.Independent.Advance50.P25.cq_chain_rule_iff_zero_basis_discord
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:57:33.53314+00:00
-- url     : https://prove2.me/theorems/914c4c67-3b89-43eb-90dc-3643d22f3d25
-- title:
--   The cq chain rule is equivalent to zero basis discord
-- statement:
--   Let $S_K$ be a concave spectral entropy family, invariant under zero padding and zero on pure densities. Let $\{|w_j\rangle\}$ be an orthonormal basis of a finite positive system $a$, let $p_j\ge0$ with $\sum_jp_j=1$, and let $\rho_{bj}$ be arbitrary density operators on a finite positive system $b$. Construct
--
--   $$
--   \rho_{ab}=\sum_jp_j|w_j\rangle\langle w_j|\otimes\rho_{bj},\qquad
--   \rho_a=\operatorname{Tr}_b\rho_{ab}.
--   $$
--
--   For the measurement in this same basis, define $\delta_K(w,b)=I_K(a:b)-\chi_K(w,b)$. Then
--
--   $$
--   S_K(\rho_{ab})=S_K(\rho_a)+\sum_jp_jS_K(\rho_{bj})
--   \quad\Longleftrightarrow\quad
--   \delta_K(w,b)=0.
--   $$
--
--   This is a statewise equivalence for a cq density. It neither optimizes discord nor characterizes zero discord of arbitrary bipartite states.
-- source:
--   Non-negative discord strengthens the subadditivity of quantum entropy functions, arXiv:1101.1717v1, PDF p. 5, §VII, unnumbered: the cq chain rule is exactly zero basis discord

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P25

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)

open QAlgorithms.Papers.Independent.Claimed50.P48 (nonzeroSpectrum)

open QAlgorithms.Papers.Independent.Gap48.P33 (discardLast)

/-- PDF p.5, §VII: statewise equivalence on the constructed cq density and its
own basis measurement. There is no optimization and no assertion for other states. -/
theorem cq_chain_rule_iff_zero_basis_discord (S : EntropyFunction) (hS : IsEntropy S)
    {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (w : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (p : A → ℝ) (rho : A → Matrix B B ℂ) (hens : DensityEnsemble p rho) :
    (S (basisCQDensity w p rho) = S (traceRight (basisCQDensity w p rho)) + ∑ j, p j * S (rho j)) ↔
      povmSpecificDiscord S (basisCQDensity w p rho) (fun j => pureDensity (w j)) = 0 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P25

end

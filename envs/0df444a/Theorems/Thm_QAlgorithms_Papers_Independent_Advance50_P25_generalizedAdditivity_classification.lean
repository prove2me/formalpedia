-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P25_generalizedAdditivity_classification
-- name    : QAlgorithms.Papers.Independent.Advance50.P25.generalizedAdditivity_classification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:58:35.539251+00:00
-- url     : https://prove2.me/theorems/07dcca37-82be-40bf-84f0-070b78860312
-- title:
--   Generalized-additivity classification within Eq. (1)
-- statement:
--   For finite-dimensional density operators, let $S$ denote von Neumann entropy in natural logarithm units, $S_Q(\rho)=1-\operatorname{Tr}\rho^2$, and
--
--   $$
--   S_{R,q}(\rho)=\frac{\log\operatorname{Tr}\rho^q}{1-q},\qquad
--   S_{T,q}(\rho)=\frac{\operatorname{Tr}\rho^q-1}{1-q},
--   $$
--
--   with both families defined to equal $S$ at $q=1$. Write $G(S_K)$ for the global cq chain rule: $S_K(\sum_jp_j|w_j\rangle\langle w_j|\otimes\rho_j)=S_K(\rho_a)+\sum_jp_jS_K(\rho_j)$ for every finite dimension, basis, normalized weights and density components, with $\rho_a$ the computed first marginal. Then
--
--   $$
--   \begin{gathered}
--   G(S),\qquad \neg G(S_Q),\\
--   \forall q\in(0,1]:\ G(S_{R,q})\Longleftrightarrow q=1,\\
--   \forall q>0:\ G(S_{T,q})\Longleftrightarrow q=1.
--   \end{gathered}
--   $$
--
--   Thus uniqueness is only within the families and parameter ranges in Eq.(1), not among all spectral entropies or rescalings of $S$.
--
--   The product-additivity distinctions in the same paragraph also hold. Writing A(S_K) for S_K(rho tensor sigma)=S_K(rho)+S_K(sigma) for every pair of finite-dimensional density operators,
--
--   $$
--   \forall q\in(0,1]:\ A(S_{R,q}),\qquad
--   \forall q>0:\ A(S_{T,q})\Longleftrightarrow q=1.
--   $$
-- source:
--   Non-negative discord strengthens the subadditivity of quantum entropy functions, arXiv:1101.1717v1, PDF p. 5, §VII, unnumbered: von Neumann entropy is unique within Eq.(1) for generalized additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P25

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)

open QAlgorithms.Papers.Independent.Claimed50.P48 (nonzeroSpectrum)

open QAlgorithms.Papers.Independent.Gap48.P33 (discardLast)

/-- PDF p.5, §VII: product additivity and generalized-additivity classification
within the four families and domains in Eq.(1). Renyi is product additive throughout
its domain; Tsallis is product additive only at q=1. Both q=1 values use the
stated limiting convention. -/
theorem generalizedAdditivity_classification :
    GeneralizedAdditive entropy ∧
    (∀ q : ℝ, 0 < q → q ≤ 1 →
      (GeneralizedAdditive (renyiEntropyNats q) ↔ q = 1) ∧
      AdditiveEntropy (renyiEntropyNats q)) ∧
    (∀ q : ℝ, 0 < q →
      (GeneralizedAdditive (tsallisEntropy q) ↔ q = 1) ∧
      (AdditiveEntropy (tsallisEntropy q) ↔ q = 1)) ∧
    ¬ GeneralizedAdditive quadraticEntropy := by sorry

end QAlgorithms.Papers.Independent.Advance50.P25

end

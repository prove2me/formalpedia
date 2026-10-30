-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P25_four_firmSubadditivity_conditions
-- name    : QAlgorithms.Papers.Independent.Advance50.P25.four_firmSubadditivity_conditions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:50:27.099514+00:00
-- url     : https://prove2.me/theorems/d5a3f683-f89b-4698-9454-f405af43e275
-- title:
--   Four equivalent firm-subadditivity properties
-- statement:
--   Let $S_K$ be a concave spectral entropy family on all finite-dimensional complex density operators, invariant under adjoining zero eigenvalues and zero on pure densities. Let $\chi_K(\{p_j,\rho_j\})=S_K(\sum_jp_j\rho_j)-\sum_jp_jS_K(\rho_j)$, with nonnegative weights summing to one. Measurement Holevo quantities use the resulting normalized conditional ensemble, and $I_K(a:b)$ uses actual partial traces.
--
--   The following properties, each quantified over all finite positive dimensions and all indicated objects, are equivalent:
--
--   $$
--   \begin{aligned}
--   \chi_K(P_a,b)&\le I_K(a:b),\\
--   \chi_K(P_a,b)&\le S_K(\rho_a),\\
--   \chi_K(N_a,b)&\le\chi_K(N_a,bc),\\
--   \chi_K(\{p_j,\mathcal E(\rho_j)\})&\le\chi_K(\{p_j,\rho_j\}).
--   \end{aligned}
--   $$
--
--   The first two range over all bipartite states and finite POVMs. The third ranges over pure tripartite states and rank-one POVMs. The fourth ranges over pure input ensembles and arbitrary completely positive trace-preserving channels. Rank-one effects need not be projectors. Zero-weight outcomes are omitted.
--
--   The equivalence provides several interchangeable entropy-level formulations of FSA.
-- source:
--   Non-negative discord strengthens the subadditivity of quantum entropy functions, arXiv:1101.1717v1, PDF p. 3, Theorem 2 (§III): four equivalent FSA conditions

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P25

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)

open QAlgorithms.Papers.Independent.Claimed50.P48 (nonzeroSpectrum)

open QAlgorithms.Papers.Independent.Gap48.P33 (discardLast)

/-- PDF p.3, Theorem 2: equivalence of entropy-level properties, not selected instances. -/
theorem four_firmSubadditivity_conditions (S : EntropyFunction) (hS : IsEntropy S) :
    (FirmlySubadditive S ↔ LocalHolevoBound S) ∧
      (LocalHolevoBound S ↔ PureDiscardMonotone S) ∧
      (PureDiscardMonotone S ↔ PureChannelMonotone S) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P25

end

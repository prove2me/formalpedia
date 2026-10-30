-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P25_four_stronger_conditions_equivalent
-- name    : QAlgorithms.Papers.Independent.Advance50.P25.four_stronger_conditions_equivalent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:52:49.577323+00:00
-- url     : https://prove2.me/theorems/d8610ffe-4939-4556-9f8f-4c3b07153d5d
-- title:
--   Generic equivalence of the four stronger properties
-- statement:
--   Let $S_K$ be a concave entropy family depending only on nonzero eigenvalues with multiplicity, invariant under adjoining zeros and vanishing on pure states. Let $\chi_K$ be its Holevo quantity, $I_K$ its mutual information, and let conditioning on $P_a$ mean averaging normalized post-measurement states with their Born probabilities. Use $K_j=\sqrt{P_{aj}}$ for the local and joint outcomes and omit zero-probability terms.
--
--   The following entropy-level properties are equivalent:
--
--   $$
--   \begin{aligned}
--   \chi_K(P_a,b)&\le I_K(a:b)-I_K(a:b\mid P_a),\\
--   \chi_K(P_a,b)&\le S_K(\rho_a)-S_K(a\mid P_a),\\
--   \chi_K(P_a,b)&\le\chi_K(P_a,bc),\\
--   \chi_K(\{p_j,\mathcal E(\rho_j)\})&\le\chi_K(\{p_j,\rho_j\}).
--   \end{aligned}
--   $$
--
--   Each property ranges over all finite positive dimensions: arbitrary bipartite states and POVMs in the first two, arbitrary tripartite states and POVMs in the third, and arbitrary density ensembles and completely positive trace-preserving channels in the fourth.
--
--   This equivalence does not assert that every such entropy satisfies these properties, and assumes neither SSA nor generalized additivity.
--
--   Each displayed global property also implies its corresponding property in Theorem 2: the first implies firm subadditivity, the second the local Holevo bound, the third the pure-state/rank-one discard bound, and the fourth the pure-input channel bound.
-- source:
--   Non-negative discord strengthens the subadditivity of quantum entropy functions, arXiv:1101.1717v1, PDF p. 3, §IV, unnumbered: generic equivalence of the four stronger conditions

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P25

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)

open QAlgorithms.Papers.Independent.Claimed50.P48 (nonzeroSpectrum)

open QAlgorithms.Papers.Independent.Gap48.P33 (discardLast)

/-- PDF p.3, §IV, paragraph before Theorem 3 (argument on p.4): generic equivalence
and implication to each corresponding Theorem 2 property, without assuming SSA.
Printed: the local/joint expressions after Eq.(8) omit division by p_j.
Changed: use normalized positive-probability outcomes and K_j=sqrt(P_j).
Why: the same paragraph's remote states and the p.4 proof require normalized
states with matching nonzero spectra; the Kraus polar unitary does not change them. -/
theorem four_stronger_conditions_equivalent (S : EntropyFunction) (hS : IsEntropy S) :
    (StrongFirmlySubadditive S ↔ StrongLocalHolevoBound S) ∧
      (StrongLocalHolevoBound S ↔ DiscardMonotone S) ∧
      (DiscardMonotone S ↔ ChannelMonotone S) ∧
      (StrongFirmlySubadditive S → FirmlySubadditive S) ∧
      (StrongLocalHolevoBound S → LocalHolevoBound S) ∧
      (DiscardMonotone S → PureDiscardMonotone S) ∧
      (ChannelMonotone S → PureChannelMonotone S) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P25

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P25_quadraticEntropy_firmSubadditivity
-- name    : QAlgorithms.Papers.Independent.Advance50.P25.quadraticEntropy_firmSubadditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:48:16.354597+00:00
-- url     : https://prove2.me/theorems/284e5271-a2a2-4e44-8bb3-dfc679c07a36
-- title:
--   Quadratic entropy is firmly subadditive
-- statement:
--   For a finite-dimensional density operator $\rho$, define quadratic entropy by $S_Q(\rho)=1-\operatorname{Tr}(\rho^2)$. All density operators below are positive semidefinite and have trace one. Write $I_Q(a:b)=S_Q(\rho_a)+S_Q(\rho_b)-S_Q(\rho_{ab})$, using actual partial traces, and let $\chi_Q$ denote the Holevo quantity computed with $S_Q$.
--
--   The following four universal properties hold:
--
--   $$
--   \begin{aligned}
--   \chi_Q(P_a,b)&\le I_Q(a:b),\\
--   \chi_Q(P_a,b)&\le S_Q(\rho_a),\\
--   \chi_Q(N_a,b)&\le\chi_Q(N_a,bc),\\
--   \chi_Q(\{p_j,\mathcal E(\rho_j)\})&\le\chi_Q(\{p_j,\rho_j\}).
--   \end{aligned}
--   $$
--
--   The first two inequalities hold for every bipartite state and every finite POVM $P_a$. The third holds for every pure tripartite state and rank-one POVM $N_a$. The fourth holds for every finite normalized ensemble of pure states and every completely positive trace-preserving channel, with arbitrary finite input and output dimensions. Zero-probability outcomes contribute zero.
--
--   These are the four equivalent firm-subadditivity properties of Theorem 2.
-- source:
--   Non-negative discord strengthens the subadditivity of quantum entropy functions, arXiv:1101.1717v1, PDF p. 4, Theorem 5 (§V); seed abstract result: quadratic entropy is firmly subadditive

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P25

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)

open QAlgorithms.Papers.Independent.Claimed50.P48 (nonzeroSpectrum)

open QAlgorithms.Papers.Independent.Gap48.P33 (discardLast)

/-- PDF p.4, Theorem 5: all four universal conclusions, for the fixed quadratic formula. -/
theorem quadraticEntropy_firmSubadditivity :
    FirmlySubadditive quadraticEntropy ∧ LocalHolevoBound quadraticEntropy ∧
      PureDiscardMonotone quadraticEntropy ∧ PureChannelMonotone quadraticEntropy := by sorry

end QAlgorithms.Papers.Independent.Advance50.P25

end

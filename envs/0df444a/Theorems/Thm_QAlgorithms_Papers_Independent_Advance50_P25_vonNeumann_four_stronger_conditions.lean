-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P25_vonNeumann_four_stronger_conditions
-- name    : QAlgorithms.Papers.Independent.Advance50.P25.vonNeumann_four_stronger_conditions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:52:00.497993+00:00
-- url     : https://prove2.me/theorems/90a26292-3dde-4a8e-a227-6a71c5a88bab
-- title:
--   Von Neumann entropy satisfies four stronger properties
-- statement:
--   Let $S(\rho)=-\operatorname{Tr}(\rho\log\rho)$ be the von Neumann entropy, using natural logarithms and $0\log0=0$, and let $\chi$ be its Holevo quantity. For a finite POVM $P_a$, write $S(a\mid P_a)=\sum_jp_jS(\rho_{aj})$ and $I(a:b\mid P_a)=\sum_jp_jI(a:b)_{\rho_{abj}}$. Positive-probability local and joint outcomes are normalized using one operator $K_j=\sqrt{P_{aj}}$ per effect; zero-probability terms are omitted.
--
--   All four universal properties hold and are equivalent:
--
--   $$
--   \begin{aligned}
--   \chi(P_a,b)&\le I(a:b)-I(a:b\mid P_a),\\
--   \chi(P_a,b)&\le S(\rho_a)-S(a\mid P_a),\\
--   \chi(P_a,b)&\le\chi(P_a,bc),\\
--   \chi(\{p_j,\mathcal E(\rho_j)\})&\le\chi(\{p_j,\rho_j\}).
--   \end{aligned}
--   $$
--
--   The first two hold for every bipartite density and finite POVM. The third permits arbitrary tripartite densities and POVMs. The fourth permits arbitrary normalized density ensembles and completely positive trace-preserving channels, with arbitrary finite dimensions.
--
--   These are stronger than the corresponding FSA conditions because the purity and rank-one restrictions have been removed and conditional terms retained.
-- source:
--   Non-negative discord strengthens the subadditivity of quantum entropy functions, arXiv:1101.1717v1, PDF p. 3, Theorem 3 (§IV): von Neumann entropy satisfies four stronger conditions

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P25

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)

open QAlgorithms.Papers.Independent.Claimed50.P48 (nonzeroSpectrum)

open QAlgorithms.Papers.Independent.Gap48.P33 (discardLast)

/-- PDF pp.3–4, Theorem 3: the fixed von Neumann entropy satisfies all four stronger
inequalities. Their equivalence is also included; no SSA hypothesis is assumed.
Printed: the local/joint expressions after Eq.(8) omit division by p_j.
Changed: normalize positive-probability outcomes and choose K_j=sqrt(P_j).
Why: the normalized remote states in the same paragraph and the p.4 proof
require trace-one conditional states; the Kraus polar unitary preserves their spectra. -/
theorem vonNeumann_four_stronger_conditions :
    (StrongFirmlySubadditive entropy ∧ StrongLocalHolevoBound entropy ∧
      DiscardMonotone entropy ∧ ChannelMonotone entropy) ∧
    (StrongFirmlySubadditive entropy ↔ StrongLocalHolevoBound entropy) ∧
    (StrongLocalHolevoBound entropy ↔ DiscardMonotone entropy) ∧
    (DiscardMonotone entropy ↔ ChannelMonotone entropy) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P25

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_squashed_monogamy
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.squashed_monogamy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:02:13.506842+00:00
-- url     : https://prove2.me/theorems/101c2a15-fc27-4f0f-9610-0c398c3c5b75
-- title:
--   Theorem 8, Eq. (13): squashed-entanglement monogamy
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   For every bipartite state, $E_{\mathrm{sq}}(A:B)=\inf_{\omega_{ABE}:\operatorname{Tr}_E\omega=\rho}\frac12 I(A;B\mid E)_\omega$, with conditional quantum mutual information $I$ in bits and all positive finite ancillary dimensions allowed. Let $\rho_{ABC}$ be any density state.
--
--   $$
--   E_{\mathrm{sq}}(\rho_{AB})+E_{\mathrm{sq}}(\rho_{AC})\le E_{\mathrm{sq}}(\rho_{A:BC}).
--   $$
--
--   The inequality assumes neither an optimal extension nor a fixed bound on its dimension.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 6, Theorem 8, Eq. (13): squashed-entanglement monogamy

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF p.6, Theorem 8, Eq.(13): the accepted half-CMI infimum over every positive finite ancillary dimension; no minimizer is assumed. -/
theorem squashed_monogamy {A : Type} {B : Type} {C : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : Op (A × (B × C))) (hrho : IsDensityMatrix rho) :
    Claimed50.P12.squashedEntanglement (marginalRA rho) +
      Claimed50.P12.squashedEntanglement (marginalRB rho) ≤
        Claimed50.P12.squashedEntanglement rho := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35

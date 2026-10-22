-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_one_way_distillation_monogamy
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.one_way_distillation_monogamy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:58:21.90241+00:00
-- url     : https://prove2.me/theorems/a7ebc684-85cb-4808-8479-eb2a056d5690
-- title:
--   Theorem 6, Eq. (11): one-way distillable-entanglement monogamy
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   Let $\rho_{ABC}$ be any density state. On the right $BC$ cooperate and send classical messages to $A$; on the left $B$ and $C$ separately send to $A$.
--
--   $$
--   E_D^{\leftarrow}(\rho_{AB})+E_D^{\leftarrow}(\rho_{AC})\le E_D^{\leftarrow}(\rho_{A:BC}).
--   $$
--
--   This monogamy statement assumes neither purity nor the existence of compatible good protocols.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 4, Theorem 6, Eq. (11): one-way distillable-entanglement monogamy

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF pp.4--5, Theorem 6, Eq.(11): one-way distillation monogamy for every tripartite state, without purity or simultaneous-protocol hypotheses. -/
theorem one_way_distillation_monogamy {A : Type} {B : Type} {C : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : Op (A × (B × C))) (hrho : IsDensityMatrix rho) :
    distillLeft (marginalRA rho) + distillLeft (marginalRB rho) ≤ distillLeft rho := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35

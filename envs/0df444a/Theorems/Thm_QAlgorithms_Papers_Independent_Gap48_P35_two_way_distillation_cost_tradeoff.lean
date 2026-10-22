-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_two_way_distillation_cost_tradeoff
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.two_way_distillation_cost_tradeoff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:02:58.525282+00:00
-- url     : https://prove2.me/theorems/5e376977-56ba-4012-922f-466238e0ff01
-- title:
--   Corollary 9, Eq. (14): two-way distillation versus joint entanglement cost
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   Let $\rho_{ABC}$ be any density state. Both distillation terms permit unrestricted two-way classical communication. The right side is singlet preparation cost across the grouped cut $A:BC$.
--
--   $$
--   E_D(\rho_{AB})+E_D(\rho_{AC})\le E_C(\rho_{A:BC}).
--   $$
--
--   This compares two-way yields to joint formation cost, without a purity restriction.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 6, Corollary 9, Eq. (14): two-way distillation versus joint entanglement cost

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF p.6, Corollary 9, Eq.(14): TWO-WAY distillation on the left and joint formation cost on the right, for arbitrary mixed states. -/
theorem two_way_distillation_cost_tradeoff {A : Type} {B : Type} {C : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : Op (A × (B × C))) (hrho : IsDensityMatrix rho) :
    distillTwoWay (marginalRA rho) + distillTwoWay (marginalRB rho) ≤ finiteSystemPreparationCost rho := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35

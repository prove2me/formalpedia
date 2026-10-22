-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_cost_distillation_tradeoff
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.cost_distillation_tradeoff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:56:42.052616+00:00
-- url     : https://prove2.me/theorems/477c50cb-603a-47ff-97b5-3ec0b8364099
-- title:
--   Theorem 5, Eq. (9): cost versus one-way distillation
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   Let $\rho_{ABC}$ be any density state. Compute its $AB$, $AC$, and $A$ marginals from that state. The distillation term permits communication $C\to A$.
--
--   $$
--   E_C(\rho_{AB})+E_D^{\leftarrow}(\rho_{AC})\le S(\rho_A).
--   $$
--
--   This retains unrestricted preparation cost and one-way distillation; the state need not be pure.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 4, Theorem 5, Eq. (9): cost versus one-way distillation

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF p.4, Theorem 5, Eq.(9): unrestricted formation cost and one-way distillation from the two marginals of the same arbitrary state. -/
theorem cost_distillation_tradeoff {A : Type} {B : Type} {C : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : Op (A × (B × C))) (hrho : IsDensityMatrix rho) :
    finiteSystemPreparationCost (marginalRA rho) + distillLeft (marginalRB rho) ≤ vnEntropy (traceRight rho) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_common_dominates_distillation
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.common_dominates_distillation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:55:59.278498+00:00
-- url     : https://prove2.me/theorems/5ed0033b-dc6d-4210-84f9-656251852dc9
-- title:
--   Proposition 4, Eq. (8): common randomness dominates one-way distillation
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   Let $\rho_{AB}$ be any density state. Both displayed rates permit only communication $B\to A$.
--
--   $$
--   E_D^{\leftarrow}(\rho_{AB})\le C_D^{\leftarrow}(\rho_{AB}).
--   $$
--
--   This compares operational net common randomness with one-way EPR distillation on the same input.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 4, Proposition 4, Eq. (8): common randomness dominates one-way distillation

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF p.4, Proposition 4, Eq.(8): net common randomness dominates distillation, both with B-to-A communication. -/
theorem common_dominates_distillation {A : Type} {B : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (rho : Op (A × B)) (hrho : IsDensityMatrix rho) :
    distillLeft rho ≤ commonLeft rho := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35

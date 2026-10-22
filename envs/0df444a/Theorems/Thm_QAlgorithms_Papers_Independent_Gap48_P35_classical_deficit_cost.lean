-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_classical_deficit_cost
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.classical_deficit_cost
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:52:13.169318+00:00
-- url     : https://prove2.me/theorems/1eb55675-24c8-453c-8913-4e40245bc721
-- title:
--   §II unnumbered: entanglement cost from loss of common randomness
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   Let $\rho_{ABC}$ be any normalized pure state. The party $BC$ cooperates in the first common-randomness task, while $B$ is traced out for the second. The deficit is formed from these two rates of the same state.
--
--   $$
--   C_D^{\leftarrow}(\rho_{A:BC})=S(\rho_A),\qquad C_D^{\leftarrow}(\rho_{A:BC})-C_D^{\leftarrow}(\rho_{AC})=E_C(\rho_{AB}).
--   $$
--
--   Thus this loss of classical correlation in rbits has the numerical value of formation cost in ebits and is independent of the chosen purification.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 3, §II unnumbered: entanglement cost from loss of common randomness

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF p.3, §II: the two classical-correlation rates are computed from the same purification; their deficit equals entanglement cost. -/
theorem classical_deficit_cost {A : Type} {B : Type} {C : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : Op (A × (B × C))) (hrho : IsDensityMatrix rho) (hpure : IsPure rho) :
    commonLeft rho = vnEntropy (traceRight rho) ∧
      classicalCorrelationDeficit rho = finiteSystemPreparationCost (marginalRA rho) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35

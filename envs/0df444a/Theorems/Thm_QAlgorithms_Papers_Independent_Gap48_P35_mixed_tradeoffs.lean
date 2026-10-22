-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_mixed_tradeoffs
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.mixed_tradeoffs
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:51:22.621903+00:00
-- url     : https://prove2.me/theorems/9f58be41-706a-42d2-9093-911bda4564c6
-- title:
--   Corollary 2, Eqs. (6)–(7): mixed-state trade-offs and pure-state saturation
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   Let $\rho_{ABC}$ be any density state, and compute all marginals by partial trace. Both displayed inequalities are equalities if $\rho_{ABC}$ is pure.
--
--   $$
--   E_f(\rho_{AB})+I^{\leftarrow}(\rho_{AC})\le S(\rho_A),\qquad E_C(\rho_{AB})+C_D^{\leftarrow}(\rho_{AC})\le S(\rho_A).
--   $$
--
--   Purity suffices for saturation; it is not required for the inequalities and is not asserted to be necessary.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 3, Corollary 2, Eqs. (6)–(7): mixed-state trade-offs and pure-state saturation

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF pp.2--3, Corollary 2, Eqs.(6)--(7): the mixed-state inequalities and both pure-state saturation clauses. -/
theorem mixed_tradeoffs {A : Type} {B : Type} {C : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : Op (A × (B × C))) (hrho : IsDensityMatrix rho) :
    (formation (marginalRA rho) + measuredCorrelation (marginalRB rho) ≤
        vnEntropy (traceRight rho)) ∧
      (finiteSystemPreparationCost (marginalRA rho) + commonLeft (marginalRB rho) ≤
        vnEntropy (traceRight rho)) ∧
      (IsPure rho →
        formation (marginalRA rho) + measuredCorrelation (marginalRB rho) =
          vnEntropy (traceRight rho) ∧
        finiteSystemPreparationCost (marginalRA rho) + commonLeft (marginalRB rho) =
          vnEntropy (traceRight rho)) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_cost_additivity_duality
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.cost_additivity_duality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:53:41.856601+00:00
-- url     : https://prove2.me/theorems/a6ce2b18-de37-494d-9fdd-aa6e839f737d
-- title:
--   §II unnumbered: equivalence of cost and common-randomness additivity
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   For $j=1,2$, let $\rho_j$ on $A_jB_j$ and $\sigma_j$ on $A_jC_j$ be complementary density states. The tensor products are grouped by party.
--
--   $$
--   E_C(\rho_1\otimes\rho_2)=E_C(\rho_1)+E_C(\rho_2)\iff C_D^{\leftarrow}(\sigma_1\otimes\sigma_2)=C_D^{\leftarrow}(\sigma_1)+C_D^{\leftarrow}(\sigma_2).
--   $$
--
--   This pins the source’s “similar relation” to the preceding pairwise additivity biconditional.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 3, §II unnumbered: equivalence of cost and common-randomness additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF p.3, §II: the pairwise additivity biconditional for cost and net distillable common randomness (the source: a similar relation). -/
theorem cost_additivity_duality {A : Type} {B : Type} {C : Type} {A2 : Type} {B2 : Type} {C2 : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C] [Fintype A2] [DecidableEq A2] [Nonempty A2] [Fintype B2] [DecidableEq B2] [Nonempty B2] [Fintype C2] [DecidableEq C2] [Nonempty C2]
    (rho : Op (A × B)) (sigma : Op (A × C))
    (rho2 : Op (A2 × B2)) (sigma2 : Op (A2 × C2))
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hrho2 : IsDensityMatrix rho2) (hsigma2 : IsDensityMatrix sigma2)
    (hcomp : BComplement rho sigma) (hcomp2 : BComplement rho2 sigma2) :
    (finiteSystemPreparationCost (Dependency50.P07.bipartiteProduct rho rho2) = finiteSystemPreparationCost rho + finiteSystemPreparationCost rho2) ↔
      (commonLeft (Dependency50.P07.bipartiteProduct sigma sigma2) =
        commonLeft sigma + commonLeft sigma2) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35

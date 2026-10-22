-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_complementarity
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.complementarity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:49:47.835609+00:00
-- url     : https://prove2.me/theorems/10417cda-7517-4e23-a610-764e498dce5d
-- title:
--   Theorem 1, Eqs. (2)–(3): complementarity of entanglement and classical correlation
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   Let the density states $\rho_{AB}$ and $\sigma_{AC}$ be complementary: they are the two indicated marginals of one normalized pure state on $ABC$.
--
--   $$
--   E_f(\rho_{AB})+I^{\leftarrow}(\sigma_{AC})=S(\rho_A),\qquad E_C(\rho_{AB})+C_D^{\leftarrow}(\sigma_{AC})=S(\rho_A).
--   $$
--
--   These are both the single-copy and the asymptotic complementarity identities.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 2, Theorem 1, Eqs. (2)–(3): complementarity of entanglement and classical correlation

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF p.2, Theorem 1, Eqs.(2)--(3): both the single-copy and operational asymptotic complementarity identities. -/
theorem complementarity {A : Type} {B : Type} {C : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : Op (A × B)) (sigma : Op (A × C))
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hcomp : BComplement rho sigma) :
    formation rho + measuredCorrelation sigma = vnEntropy (traceRight rho) ∧
      finiteSystemPreparationCost rho + commonLeft sigma = vnEntropy (traceRight rho) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35

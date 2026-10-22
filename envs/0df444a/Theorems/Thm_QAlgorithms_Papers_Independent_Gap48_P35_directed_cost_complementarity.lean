-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_directed_cost_complementarity
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.directed_cost_complementarity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:54:30.401701+00:00
-- url     : https://prove2.me/theorems/f4575931-73bb-4f29-9905-951cef4d13b2
-- title:
--   §II unnumbered: directed cost complementarity
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   Let $\sigma_{AC}$ complement the density state $\rho_{AB}$. The directed formation costs restrict preparation communication to $A\to B$ and $B\to A$, respectively, using the actual consumed singlets.
--
--   $$
--   E_C^{\rightarrow}(\rho_{AB})+C_D^{\leftarrow}(\sigma_{AC})=S(\rho_A),\qquad E_C^{\rightarrow}(\rho_{AB})=E_C^{\leftarrow}(\rho_{AB})=E_C(\rho_{AB}).
--   $$
--
--   The direction restrictions are defined operationally; equality with unrestricted cost is a conclusion.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 3, §II unnumbered: directed cost complementarity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF p.3, §II: directed complementarity and equality of the two operationally restricted formation costs with the unrestricted cost. -/
theorem directed_cost_complementarity {A : Type} {B : Type} {C : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : Op (A × B)) (sigma : Op (A × C))
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hcomp : BComplement rho sigma) :
    forwardCost rho + commonLeft sigma = vnEntropy (traceRight rho) ∧
      forwardCost rho = forwardCost (Dependency50.P19.flip rho) ∧
      forwardCost (Dependency50.P19.flip rho) = finiteSystemPreparationCost rho := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35

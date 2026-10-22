-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_classical_deficit_symmetry
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.classical_deficit_symmetry
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:55:19.316446+00:00
-- url     : https://prove2.me/theorems/08e530ab-bfb2-467b-9548-6dd276fcace3
-- title:
--   Corollary 3: symmetry of classical-correlation deficits
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   Let $\sigma_{AC}$ complement the density state $\rho_{AB}$. Here both right arrows mean communication from $A$ to the second party, $B$ or $C$.
--
--   $$
--   S(\rho_B)-C_D^{\rightarrow}(\rho_{AB})=S(\sigma_C)-C_D^{\rightarrow}(\sigma_{AC}).
--   $$
--
--   The deficits concern the entropies of the two second parties, not the entropy of $A$.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 3, Corollary 3: symmetry of classical-correlation deficits

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF p.3, Corollary 3: BOTH source arrows point RIGHT; each commonLeft is therefore applied to the swapped state. -/
theorem classical_deficit_symmetry {A : Type} {B : Type} {C : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : Op (A × B)) (sigma : Op (A × C))
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hcomp : BComplement rho sigma) :
    vnEntropy (traceLeft rho) - commonLeft (Dependency50.P19.flip rho) =
      vnEntropy (traceLeft sigma) - commonLeft (Dependency50.P19.flip sigma) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35

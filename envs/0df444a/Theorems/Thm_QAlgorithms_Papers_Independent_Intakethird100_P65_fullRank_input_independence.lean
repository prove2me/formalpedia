-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_fullRank_input_independence
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.fullRank_input_independence
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:44:00.141473+00:00
-- url     : https://prove2.me/theorems/8dd74b36-0c41-4fe7-84ec-c9618a948121
-- title:
--   Remark 2 / Eq.(27): input independence at full rank
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $\mathcal N:A'\to B$ be CPTP, with $A$ a reference copy of $A'$. Let $|\psi\rangle_{AA'}$ be a unit vector whose input marginal is positive definite. With $\Phi_{AA'}$ the normalized maximally entangled state,
--
--   $$I_{\max}(\mathcal N)=I_{\max}(A:B)_{(\mathrm{id}_A\otimes\mathcal N)(|\psi\rangle\langle\psi|)}.$$
--
--   The left side is defined using $\Phi$. Thus every full-rank purified input gives the same channel max-information. The claim is not extended to rank-deficient input marginals.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 8, Remark 2 / Eq.(27): input independence at full rank

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P65

noncomputable section

open Filter QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakethird100.P65

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (transposeBob)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Independent2.P01 (dampingKraus damping)

open QAlgorithms.Papers.Independent.Gap48.P33 (phaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P62 (Stochastic)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized purifiedDistance)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer permute)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond channelPower channelRelative)

open QAlgorithms.Papers.Independent.Support50.P39 (quantumMutualInformation)

variable {A B C D R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty R]

/-- Remark 2, Eq.(27), PDF p.8: full rank is essential. The reference is a
copy of the input; any normalized pure purification is allowed. -/
theorem fullRank_input_independence (N : Superop A B) (hN : IsChannel N)
    (psi : EuclideanSpace ℂ (A × A)) (hpsi : ‖psi‖ = 1)
    (hfull : (traceLeft (pureDensity psi)).PosDef) :
    (channelInfo N : EReal) = maxInfo (idTensorSuperop N (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_mutual_chi_identity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.mutual_chi_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:29:32.940373+00:00
-- url     : https://prove2.me/theorems/9be42266-5f9d-4d9f-8fbe-88f052b532aa
-- title:
--   Unnumbered main identity (29)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $\widehat\Phi$ be complementary to $\Phi$, obtained by the other partial trace of the same Stinespring isometry. For every input state $\rho$ with finite entropy,
--
--   $$I(\rho,\Phi)+C_\chi(\widehat\Phi,\rho)=H(\rho)+C_\chi(\Phi,\rho).$$
--
--   This expresses channel mutual information through fixed-average Holevo capacities, even when both output entropies are infinite.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 13, Unnumbered main identity (29)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Identity (29), PDF p.13: additive equivalent, with only INPUT entropy finite. -/
theorem mutual_chi_identity {I J K : Type} [Countable I] [Countable J] [Countable K]
    [Nonempty I] [Nonempty J] [Nonempty K] (Phi : MI.Channel I J) (Psi : MI.Channel I K)
    (hcomp : MI.Complementary Phi Psi) (rho : State I)
    (hfinite : MI.homogeneousEntropy rho.coefficients < ⊤) :
    MI.mutualInformation rho.coefficients Phi.val + Ens.stateChi Psi.val rho =
      MI.homogeneousEntropy rho.coefficients + Ens.stateChi Phi.val rho := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end

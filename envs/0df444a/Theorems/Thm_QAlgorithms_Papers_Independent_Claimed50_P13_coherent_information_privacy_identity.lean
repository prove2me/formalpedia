-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_coherent_information_privacy_identity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.coherent_information_privacy_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:39:16.88406+00:00
-- url     : https://prove2.me/theorems/28f0f83a-808b-43b9-bb80-b48be866be56
-- title:
--   Proposition 4, (36): coherent information equals privacy difference
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $\widehat\Phi$ be complementary to $\Phi$, obtained by the other partial trace of the same Stinespring isometry. Let $\rho$ have finite entropy, and let $\mu$ be any generalized ensemble carried by pure states with barycenter $\rho$. Then
--
--   $$\chi_\Phi(\mu)-\chi_{\widehat\Phi}(\mu)=I(\rho,\Phi)-H(\rho)=I_c(\rho,\Phi).$$
--
--   This relates signed private classical information to coherent information for every pure-state decomposition of a fixed input.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 19, Proposition 4, (36): coherent information equals privacy difference

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 4, (36), PDF pp.19--20. The p.19 standing assumption is finite
input entropy. Signed REAL differences remain signed; output entropies may be infinite. -/
theorem coherent_information_privacy_identity {I J K : Type}
    [Countable I] [Countable J] [Countable K] [Nonempty I] [Nonempty J] [Nonempty K]
    (Phi : MI.Channel I J) (Psi : MI.Channel I K) (hcomp : MI.Complementary Phi Psi)
    (rho : State I) (hfinite : MI.homogeneousEntropy rho.coefficients < ⊤)
    (mu : Ens.GeneralizedEnsemble I) (haverage : Ens.HasAverage mu rho)
    (hpure : ∀ᵐ sigma ∂(mu : Measure (State I)), sigma ∈ Ens.pureStates I) :
    (Ens.ensembleHolevo Phi.val mu).toReal - (Ens.ensembleHolevo Psi.val mu).toReal =
      (MI.mutualInformation rho.coefficients Phi.val).toReal -
        (MI.homogeneousEntropy rho.coefficients).toReal ∧
    (Ens.ensembleHolevo Phi.val mu).toReal - (Ens.ensembleHolevo Psi.val mu).toReal =
      MI.finiteInputCoherentInfo rho.coefficients Phi.val := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end

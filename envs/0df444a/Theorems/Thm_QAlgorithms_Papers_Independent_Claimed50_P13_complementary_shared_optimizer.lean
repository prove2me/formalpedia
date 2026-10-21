-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_complementary_shared_optimizer
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.complementary_shared_optimizer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:39:54.871464+00:00
-- url     : https://prove2.me/theorems/e3cad817-8c75-4139-aefc-78ec9d3880fa
-- title:
--   Unnumbered assertion after Proposition 4: shared optimizers
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $\widehat\Phi$ be complementary to $\Phi$, obtained by the other partial trace of the same Stinespring isometry. Let $H(\rho)<\infty$ and let $\mu$ be a pure-state generalized ensemble with barycenter $\rho$. The same ensemble attains either fixed-average Holevo supremum exactly when it attains the other:
--
--   $$\chi_\Phi(\mu)=C_\chi(\Phi,\rho)\quad\Longleftrightarrow\quad\chi_{\widehat\Phi}(\mu)=C_\chi(\widehat\Phi,\rho).$$
--
--   This transfers attainment between complementary channels without changing the pure-state optimizing measure.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 20, Unnumbered assertion after Proposition 4: shared optimizers

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Shared optimizer consequence, PDF p.20. The SAME PURE ensemble optimizes
either channel iff it optimizes the other. Pure support is inherited from p.19;
the assertion would be false for arbitrary mixed-state measures. -/
theorem complementary_shared_optimizer {I J K : Type}
    [Countable I] [Countable J] [Countable K] [Nonempty I] [Nonempty J] [Nonempty K]
    (Phi : MI.Channel I J) (Psi : MI.Channel I K) (hcomp : MI.Complementary Phi Psi)
    (rho : State I) (hfinite : MI.homogeneousEntropy rho.coefficients < ⊤)
    (mu : Ens.GeneralizedEnsemble I) (haverage : Ens.HasAverage mu rho)
    (hpure : ∀ᵐ sigma ∂(mu : Measure (State I)), sigma ∈ Ens.pureStates I) :
    Ens.ensembleHolevo Phi.val mu = Ens.stateChi Phi.val rho ↔
      Ens.ensembleHolevo Psi.val mu = Ens.stateChi Psi.val rho := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end

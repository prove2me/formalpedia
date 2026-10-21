-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_non_cq_full_average_strictness
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.non_cq_full_average_strictness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:35:41.586402+00:00
-- url     : https://prove2.me/theorems/fba83423-a13a-4528-855e-ff88f35d645c
-- title:
--   Corollary 1, independently valid alternative 1
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $F$ be a nonnegative densely defined self-adjoint input observable and let $E>0$ be finite. Write $K_{F,E}=\{\rho:\operatorname{Tr}\rho F\le E\}$, with the energy expectation understood in the extended spectral-cutoff sense. Assume $H(\rho)<\infty$ for every $\rho\in K_{F,E}$. Suppose an optimal generalized ensemble $\mu_*$ has a faithful average state, and $\Phi$ is not a discrete c-q channel. Then
--
--   $$C_\chi(\Phi,F,E)<C_{\rm ea}(\Phi,F,E).$$
--
--   The statement concerns the channel quantities themselves; the assisted capacity is defined independently through block encodings with an average-message energy constraint.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 16, Corollary 1, independently valid alternative 1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Corollary 1, alternative 1 ONLY, PDF p.16. The complete two-alternative
corollary is separately deferred. Nondegenerate means full support. -/
theorem non_cq_full_average_strictness {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : MI.Channel I J) (F : PositiveObservable I) (E : ℝ) (hE : 0 < E)
    (hfinite : FiniteEntropyConstraint F E) (mu : Ens.GeneralizedEnsemble I)
    (hoptimal : Ens.IsCapacityAttaining Phi.val (feasibleStates F E) mu)
    (hfull : MI.operatorKernel (Ens.averageCoefficients mu) = {0})
    (hnotcq : ¬ IsDiscreteCQ Phi.val) :
    chiCapacity Phi.val F E < operationalAssistedCapacity Phi.val F E := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end

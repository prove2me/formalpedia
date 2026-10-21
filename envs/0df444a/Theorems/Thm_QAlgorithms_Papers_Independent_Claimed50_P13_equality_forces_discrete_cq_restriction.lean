-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_equality_forces_discrete_cq_restriction
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.equality_forces_discrete_cq_restriction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:34:22.095275+00:00
-- url     : https://prove2.me/theorems/f3f4018d-2003-40c5-802c-1b47557954e1
-- title:
--   Theorem 2: equality forces a discrete c-q restriction
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $F$ be a nonnegative densely defined self-adjoint input observable and let $E>0$ be finite. Write $K_{F,E}=\{\rho:\operatorname{Tr}\rho F\le E\}$, with the energy expectation understood in the extended spectral-cutoff sense. Assume $H(\rho)<\infty$ for every $\rho\in K_{F,E}$. Let $\mu_*$ be any generalized optimal ensemble and set $H_*=\operatorname{supp}\overline\rho(\mu_*)$. Then
--
--   $$C_\chi(\Phi,F,E)=C_{\rm ea}(\Phi,F,E)\ \Longrightarrow\ \Phi|_{\mathfrak S(H_*)}\text{ is a discrete c-q channel}.$$
--
--   This identifies the precise input support on which equality forces a classical preparation structure.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 15, Theorem 2: equality forces a discrete c-q restriction

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 2, PDF p.15: arbitrary optimal generalized ensemble, with its own
average and support. No pure-support premise is added to the optimizer. -/
theorem equality_forces_discrete_cq_restriction {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : MI.Channel I J) (F : PositiveObservable I) (E : ℝ) (hE : 0 < E)
    (hfinite : FiniteEntropyConstraint F E) (mu : Ens.GeneralizedEnsemble I)
    (hoptimal : Ens.IsCapacityAttaining Phi.val (feasibleStates F E) mu)
    (heq : chiCapacity Phi.val F E = operationalAssistedCapacity Phi.val F E) :
    DiscreteCQOnSupport Phi.val (Ens.averageCoefficients mu) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end

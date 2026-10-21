-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_constrained_assisted_coding
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.constrained_assisted_coding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:26:27.896504+00:00
-- url     : https://prove2.me/theorems/94a997d8-ca44-41a4-8773-650c395a1c33
-- title:
--   Theorem 1, (14): general constrained entanglement-assisted coding theorem
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $F$ be a nonnegative densely defined self-adjoint input observable and let $E>0$ be finite. Write $K_{F,E}=\{\rho:\operatorname{Tr}\rho F\le E\}$, with the energy expectation understood in the extended spectral-cutoff sense. For a channel $\Phi$, its constrained entanglement-assisted capacity, possibly infinite, satisfies
--
--   $$C_{\rm ea}(\Phi,F,E)=\sup_{\rho\in K_{F,E}}I(\rho,\Phi).$$
--
--   The statement concerns the channel quantities themselves; the assisted capacity is defined independently through block encodings with an average-message energy constraint.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 6, Theorem 1, (14): general constrained entanglement-assisted coding theorem

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 1, (14), PDF pp.6--7. No Gibbs, compactness or entropy premise.
Empty feasible sets use zero nonnegative suprema and zero achievable rate. -/
theorem constrained_assisted_coding {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] (Phi : MI.Channel I J) (F : PositiveObservable I)
    (E : ℝ) (hE : 0 < E) :
    operationalAssistedCapacity Phi.val F E = informationSupremum Phi.val F E := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end

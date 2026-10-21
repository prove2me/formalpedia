-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_unconstrained_assisted_coding
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.unconstrained_assisted_coding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:27:36.326812+00:00
-- url     : https://prove2.me/theorems/93cfd689-ec3a-4785-aa6a-1966e3a64946
-- title:
--   Unnumbered consequence of Theorem 1: unconstrained capacity
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $\Phi$ have input space $H_A$. Its unconstrained assisted capacity satisfies
--
--   $$C_{\rm ea}(\Phi)=\sup_{\rho\in\mathfrak S(H_A)}I(\rho,\Phi)\in[0,\infty].$$
--
--   The statement concerns the channel quantities themselves; the assisted capacity is defined independently through block encodings with an average-message energy constraint.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 7, Unnumbered consequence of Theorem 1: unconstrained capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Unnumbered consequence of Theorem 1, PDF p.7: supremum over INPUT states. -/
theorem unconstrained_assisted_coding {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] (Phi : MI.Channel I J) :
    unconstrainedAssistedCapacity Phi.val =
      ⨆ rho : State I, MI.mutualInformation rho.coefficients Phi.val := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end

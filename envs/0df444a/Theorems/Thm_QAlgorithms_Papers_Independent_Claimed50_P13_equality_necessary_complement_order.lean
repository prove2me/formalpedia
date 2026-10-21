-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_equality_necessary_complement_order
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.equality_necessary_complement_order
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:32:59.641105+00:00
-- url     : https://prove2.me/theorems/64adefd9-cfc3-4065-8969-3c70c2c4567d
-- title:
--   Unnumbered necessary comparisons following (31)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $F$ be a nonnegative densely defined self-adjoint input observable and let $E>0$ be finite. Write $K_{F,E}=\{\rho:\operatorname{Tr}\rho F\le E\}$, with the energy expectation understood in the extended spectral-cutoff sense. Assume $H(\rho)<\infty$ for every $\rho\in K_{F,E}$. Let $\widehat\Phi$ be complementary to $\Phi$, obtained by the other partial trace of the same Stinespring isometry. The following two necessary conditions hold:
--
--   $$C_{\rm ea}(\Phi,F,E)=C_\chi(\Phi,F,E)\ \Longrightarrow\ C_\chi(\Phi,F,E)\le C_\chi(\widehat\Phi,F,E),$$
--   $$C_{\rm ea}(\Phi,F,E)=C(\Phi,F,E)\ \Longrightarrow\ C(\Phi,F,E)\le C(\widehat\Phi,F,E).$$
--
--   The statement concerns the channel quantities themselves; the assisted capacity is defined independently through block encodings with an average-message energy constraint.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 13, Unnumbered necessary comparisons following (31)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Necessary comparisons after (31), PDF p.13. Both implications, no converses. -/
theorem equality_necessary_complement_order {I J K : Type}
    [Countable I] [Countable J] [Countable K] [Nonempty I] [Nonempty J] [Nonempty K]
    (Phi : MI.Channel I J) (Psi : MI.Channel I K) (hcomp : MI.Complementary Phi Psi)
    (F : PositiveObservable I) (E : ℝ) (hE : 0 < E)
    (hfinite : FiniteEntropyConstraint F E) :
    (operationalAssistedCapacity Phi.val F E = chiCapacity Phi.val F E →
      chiCapacity Phi.val F E ≤ chiCapacity Psi.val F E) ∧
    (operationalAssistedCapacity Phi.val F E = regularizedUnassistedCapacity Phi.val F E →
      regularizedUnassistedCapacity Phi.val F E ≤ regularizedUnassistedCapacity Psi.val F E) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end

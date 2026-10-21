-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_capacity_complement_bounds
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.capacity_complement_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:31:07.032978+00:00
-- url     : https://prove2.me/theorems/8cfdfb9b-f430-46fb-8af1-8b268e5cffc4
-- title:
--   Proposition 1, both inequalities (31)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $F$ be a nonnegative densely defined self-adjoint input observable and let $E>0$ be finite. Write $K_{F,E}=\{\rho:\operatorname{Tr}\rho F\le E\}$, with the energy expectation understood in the extended spectral-cutoff sense. Assume $H(\rho)<\infty$ for every $\rho\in K_{F,E}$. Let $\widehat\Phi$ be complementary to $\Phi$, obtained by the other partial trace of the same Stinespring isometry. Both inequalities hold:
--
--   $$2C_\chi(\Phi,F,E)\le C_{\rm ea}(\Phi,F,E)+C_\chi(\widehat\Phi,F,E),$$
--   $$2C(\Phi,F,E)\le C_{\rm ea}(\Phi,F,E)+C(\widehat\Phi,F,E).$$
--
--   The statement concerns the channel quantities themselves; the assisted capacity is defined independently through block encodings with an average-message energy constraint.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 13, Proposition 1, both inequalities (31)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 1, BOTH inequalities (31), PDF pp.13--14. Additive forms preserve
the printed differences since Section 4 makes all capacities finite. -/
theorem capacity_complement_bounds {I J K : Type}
    [Countable I] [Countable J] [Countable K] [Nonempty I] [Nonempty J] [Nonempty K]
    (Phi : MI.Channel I J) (Psi : MI.Channel I K) (hcomp : MI.Complementary Phi Psi)
    (F : PositiveObservable I) (E : ℝ) (hE : 0 < E)
    (hfinite : FiniteEntropyConstraint F E) :
    2 * chiCapacity Phi.val F E ≤ operationalAssistedCapacity Phi.val F E + chiCapacity Psi.val F E ∧
    2 * regularizedUnassistedCapacity Phi.val F E ≤
      operationalAssistedCapacity Phi.val F E + regularizedUnassistedCapacity Psi.val F E := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_noiseless_sharpness
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.noiseless_sharpness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:32:09.680879+00:00
-- url     : https://prove2.me/theorems/533a966f-a0e9-4356-8b6d-9a7893df9450
-- title:
--   Unnumbered sharpness after Proposition 1
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $F$ be a nonnegative densely defined self-adjoint input observable and let $E>0$ be finite. Write $K_{F,E}=\{\rho:\operatorname{Tr}\rho F\le E\}$, with the energy expectation understood in the extended spectral-cutoff sense. Assume $H(\rho)<\infty$ for every $\rho\in K_{F,E}$. Let $\Phi=\operatorname{Id}_A$ and let $\Psi(X)=\operatorname{Tr}(X)\tau$, where $\tau$ is a pure state on a one-dimensional environment. Both inequalities of Proposition 1 become equalities:
--
--   $$2C_\chi(\operatorname{Id}_A,F,E)=C_{\rm ea}(\operatorname{Id}_A,F,E)+C_\chi(\Psi,F,E),$$
--   $$2C(\operatorname{Id}_A,F,E)=C_{\rm ea}(\operatorname{Id}_A,F,E)+C(\Psi,F,E).$$
--
--   The statement concerns the channel quantities themselves; the assisted capacity is defined independently through block encodings with an average-message energy constraint.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 13, Unnumbered sharpness after Proposition 1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Noiseless sharpness after (31), PDF p.13: BOTH equalities, with the
pure-replacer complement constructed explicitly. -/
theorem noiseless_sharpness {I : Type} [Countable I] [Nonempty I]
    (F : PositiveObservable I) (E : ℝ) (hE : 0 < E)
    (hfinite : FiniteEntropyConstraint F E) (tau : PureState Unit) :
    2 * chiCapacity (id : Matrix I I ℂ → Matrix I I ℂ) F E =
      operationalAssistedCapacity id F E + chiCapacity (pureReplacer (I := I) tau) F E ∧
    2 * regularizedUnassistedCapacity (id : Matrix I I ℂ → Matrix I I ℂ) F E =
      operationalAssistedCapacity id F E + regularizedUnassistedCapacity (pureReplacer (I := I) tau) F E := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end

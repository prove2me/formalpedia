-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_assisted_capacity_lower_semicontinuity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.assisted_capacity_lower_semicontinuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:36:39.759755+00:00
-- url     : https://prove2.me/theorems/1c428ff8-8e87-47a1-b041-05f4e5b06dfb
-- title:
--   Section 5 unnumbered main result: strong lower semicontinuity
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $F$ be a nonnegative densely defined self-adjoint input observable and let $E>0$ be finite. Write $K_{F,E}=\{\rho:\operatorname{Tr}\rho F\le E\}$, with the energy expectation understood in the extended spectral-cutoff sense. The extended function $\Phi\mapsto C_{\rm ea}(\Phi,F,E)$ is lower semicontinuous in the strong channel topology. In particular, whenever $\Phi_n\to\Phi_0$ pointwise in output trace norm on every input state,
--
--   $$C_{\rm ea}(\Phi_0,F,E)\le\liminf_{n\to\infty}C_{\rm ea}(\Phi_n,F,E).$$
--
--   The statement concerns the channel quantities themselves; the assisted capacity is defined independently through block encodings with an average-message energy constraint.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 17, Section 5 unnumbered main result: strong lower semicontinuity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section 5 main assertion, PDF p.17: topological lower semicontinuity AND
its ENNReal sequential specialization. No Gibbs, compactness or entropy premise. -/
theorem assisted_capacity_lower_semicontinuity {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (F : PositiveObservable I) (E : ℝ) (hE : 0 < E) :
    LowerSemicontinuous (fun Phi : MI.Channel I J => operationalAssistedCapacity Phi.val F E) ∧
    ∀ (Phi : ℕ → MI.Channel I J) (Phi0 : MI.Channel I J),
      Op.StronglyConverges (fun n => (Phi n).val) Phi0.val →
      operationalAssistedCapacity Phi0.val F E ≤
        Filter.liminf (fun n => operationalAssistedCapacity (Phi n).val F E) atTop := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end

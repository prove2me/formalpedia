-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_kraus_capacity_continuity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.kraus_capacity_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:38:35.264992+00:00
-- url     : https://prove2.me/theorems/12a42a01-fd3c-4f54-bfbb-7175c99a389c
-- title:
--   Section 5 countable Kraus continuity application
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $F$ be a nonnegative densely defined self-adjoint input observable and let $E>0$ be finite. Write $K_{F,E}=\{\rho:\operatorname{Tr}\rho F\le E\}$, with the energy expectation understood in the extended spectral-cutoff sense. Let normalized countable Kraus families $V^n=(V_i^n)_i$ converge strongly to $V^0$ for each $i$, with $\sum_i\|V_i^n u\|^2=\|u\|^2$ also for $n=0$. Put
--
--   $$\Phi_n(X)=\sum_i V_i^nX(V_i^n)^*,\qquad[\widehat\Phi_n(X)]_{ij}=\operatorname{Tr}V_i^nX(V_j^n)^*.$$
--   Both formulas define complementary channels and both sequences converge strongly to their $n=0$ channels. For every positive constraint observable $F$ and finite $E>0$ satisfying the Gibbs trace condition at every positive inverse temperature, moreover,
--
--   $$C_{\rm ea}(\Phi_n,F,E)\longrightarrow C_{\rm ea}(\Phi_0,F,E)<\infty.$$
--
--   The statement concerns the channel quantities themselves; the assisted capacity is defined independently through block encodings with an average-message energy constraint.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 18, Section 5 countable Kraus continuity application

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Countable Kraus continuity, PDF p.18: only V_i converge strongly, not their
adjoints. Includes both channels, SAME-dilation complements and capacity limit. -/
theorem kraus_capacity_continuity {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] (V : ℕ → MI.KrausFamily I J) (V0 : MI.KrausFamily I J)
    (hV : ∀ i u, Tendsto (fun n => (V n).val i u) atTop (𝓝 (V0.val i u))) :
    (∀ n, IsTraceClassChannel (MI.countableKrausAction (V n)) ∧
      IsTraceClassChannel (krausComplementAction (V n)) ∧
      ComplementaryMaps (MI.countableKrausAction (V n)) (krausComplementAction (V n))) ∧
    IsTraceClassChannel (MI.countableKrausAction V0) ∧
    IsTraceClassChannel (krausComplementAction V0) ∧
    ComplementaryMaps (MI.countableKrausAction V0) (krausComplementAction V0) ∧
    Op.StronglyConverges (fun n => MI.countableKrausAction (V n)) (MI.countableKrausAction V0) ∧
    Op.StronglyConverges (fun n => krausComplementAction (V n)) (krausComplementAction V0) ∧
    ∀ (F : PositiveObservable I) (E : ℝ), 0 < E → GibbsCondition F →
    operationalAssistedCapacity (MI.countableKrausAction V0) F E < ⊤ ∧
    Tendsto (fun n => operationalAssistedCapacity (MI.countableKrausAction (V n)) F E) atTop
      (𝓝 (operationalAssistedCapacity (MI.countableKrausAction V0) F E)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_finite_kraus_optimal_ensemble
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.finite_kraus_optimal_ensemble
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:33:52.522316+00:00
-- url     : https://prove2.me/theorems/250e1f49-e82c-4661-b92b-fc691a16ae9d
-- title:
--   Unnumbered existence application: finite Kraus rank
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $F$ be a nonnegative densely defined self-adjoint input observable and let $E>0$ be finite. Write $K_{F,E}=\{\rho:\operatorname{Tr}\rho F\le E\}$, with the energy expectation understood in the extended spectral-cutoff sense. Assume $K_{F,E}\ne\varnothing$, $\operatorname{Tr}e^{-\lambda F}<\infty$ for every $\lambda>0$, and $\Phi$ has finitely many Kraus summands. Then $K_{F,E}$ is compact, the output entropy is finite and continuous there, and a generalized optimal ensemble exists:
--
--   $$\exists\mu_*:\quad\overline\rho(\mu_*)\in K_{F,E},\qquad\chi_\Phi(\mu_*)=C_\chi(\Phi,F,E).$$
--
--   The statement concerns the channel quantities themselves; the assisted capacity is defined independently through block encodings with an average-message energy constraint.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 15, Unnumbered existence application: finite Kraus rank

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Finite Kraus application after Proposition 2, PDF p.15. Printed: feasibility
unstated. Changed: nonempty constraint, necessary for a probability optimizer.
Finite-valued output entropy continuity is included. Independent review pending. -/
theorem finite_kraus_optimal_ensemble {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] (Phi : MI.Channel I J) (F : PositiveObservable I)
    (E : ℝ) (hE : 0 < E) (hfeasible : (feasibleStates F E).Nonempty)
    (hGibbs : GibbsCondition F) (hkraus : HasFiniteKrausRepresentation Phi.val) :
    IsCompact (feasibleStates F E) ∧
    (∀ rho ∈ feasibleStates F E, MI.homogeneousEntropy (Phi.val rho.coefficients) < ⊤) ∧
    ContinuousOn (fun rho : State I => (MI.homogeneousEntropy (Phi.val rho.coefficients)).toReal)
      (feasibleStates F E) ∧
    ∃ mu : Ens.GeneralizedEnsemble I,
      Ens.IsCapacityAttaining Phi.val (feasibleStates F E) mu := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end

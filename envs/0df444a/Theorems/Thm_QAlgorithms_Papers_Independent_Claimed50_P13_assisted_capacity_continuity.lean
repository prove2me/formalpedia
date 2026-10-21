-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_assisted_capacity_continuity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.assisted_capacity_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:37:48.46264+00:00
-- url     : https://prove2.me/theorems/e9dc3482-b4be-475e-ac52-ab42ab936531
-- title:
--   Proposition 3: two sufficient conditions for continuity
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. Write $H$ for von Neumann entropy, $I(\rho,\Phi)$ for the relative-entropy mutual information of a purified input, and $C_\chi$, $C$, $C_{\rm ea}$ for the single-use Holevo, regularized classical and assisted classical capacities, respectively. A second argument $\rho$ in $C_\chi(\Phi,\rho)$ fixes the exact input average. Let $F$ be a nonnegative densely defined self-adjoint input observable and let $E>0$ be finite. Write $K_{F,E}=\{\rho:\operatorname{Tr}\rho F\le E\}$, with the energy expectation understood in the extended spectral-cutoff sense. Assume $\operatorname{Tr}e^{-\lambda F}<\infty$ for every $\lambda>0$ and $\Phi_n\to\Phi_0$ strongly. Assume either (1) for every sequence $\rho_n\in K_{F,E}$ tending in trace norm to $\rho_0\in K_{F,E}$, the output entropies converge to $H(\Phi_0(\rho_0))<\infty$; or (2) there are complementary channels $\widehat\Phi_n$ and $\widehat\Phi_0$ on one fixed separable environment, with $\widehat\Phi_n\to\widehat\Phi_0$ strongly. Then
--
--   $$C_{\rm ea}(\Phi_n,F,E)\longrightarrow C_{\rm ea}(\Phi_0,F,E)<\infty.$$
--
--   The statement concerns the channel quantities themselves; the assisted capacity is defined independently through block encodings with an average-message energy constraint.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 17, Proposition 3: two sufficient conditions for continuity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 3, BOTH sufficient conditions, PDF pp.17--19. Condition 1 uses
the finite-entropy reading of its p.19 proof. Condition 2 includes all pairs,
including the limiting pair, on one fixed separable environment. -/
theorem assisted_capacity_continuity {I J K : Type}
    [Countable I] [Countable J] [Countable K] [Nonempty I] [Nonempty J] [Nonempty K]
    (F : PositiveObservable I) (E : ℝ) (hE : 0 < E) (hGibbs : GibbsCondition F)
    (Phi : ℕ → MI.Channel I J) (Phi0 : MI.Channel I J)
    (hstrong : Op.StronglyConverges (fun n => (Phi n).val) Phi0.val)
    (hcondition : OutputEntropyCondition Phi Phi0 F E ∨
      ∃ (Psi : ℕ → MI.Channel I K) (Psi0 : MI.Channel I K),
        Op.StronglyConverges (fun n => (Psi n).val) Psi0.val ∧
        (∀ n, MI.Complementary (Phi n) (Psi n)) ∧ MI.Complementary Phi0 Psi0) :
    operationalAssistedCapacity Phi0.val F E < ⊤ ∧
    Tendsto (fun n => operationalAssistedCapacity (Phi n).val F E) atTop
      (𝓝 (operationalAssistedCapacity Phi0.val F E)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end

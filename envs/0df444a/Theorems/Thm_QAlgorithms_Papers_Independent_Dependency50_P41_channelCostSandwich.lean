-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_channelCostSandwich
-- name    : QAlgorithms.Papers.Independent.Dependency50.P41.channelCostSandwich
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:52:18.288795+00:00
-- url     : https://prove2.me/theorems/adede4e1-fe99-4c1b-9f14-90072f188342
-- title:
--   Channel cost between output state cost and output formation
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces of positive dimension. Logarithms and entropies are in bits. Let $\mathcal E:A\to B$ be CPTP and $A^\prime\cong A$. The channel cost $E_C(\mathcal E)$ is the infimum of asymptotic LOCC simulation rates: Alice initially holds the entire input and one half of a normalized maximally entangled state of Schmidt rank $M_n$, Bob holds the other half, Alice has no required output, and Bob receives the output. One protocol at each block length approximates the whole channel $\mathcal E^{\otimes n}$ in full diamond norm, with error tending to zero; its rate is $\limsup_n\log_2 M_n/n$. For a normalized bipartite state $\omega$, $E_F(\omega)$ is the infimum of the average marginal von Neumann entropy over normalized pure-state probability ensembles representing $\omega$. For a normalized bipartite state $\omega$, $E_C(\omega)$ is independently defined by LOCC preparation of $\omega^{\otimes n}$ from Schmidt-rank-$M_n$ maximally entangled resources, with trace-norm error tending to zero and rate $\limsup_n\log_2 M_n/n$. Both pure-input maxima below are attained, and $$\max_{\psi\in\mathcal V(AA^\prime)}E_C\bigl((\mathcal E\otimes I)(\psi)\bigr)\le E_C(\mathcal E)\le\max_{\psi\in\mathcal V(AA^\prime)}E_F\bigl((\mathcal E\otimes I)(\psi)\bigr).$$
--
--   This distinguishes operational state and channel costs from entanglement of formation.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, PDF p. 13, Corollary 17

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P41

open scoped ComplexConjugate Matrix ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble formation pureAverage)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC spinFlip concurrence)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy groupedPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1108.5357v3, PDF p.13, Corollary 17, (69).
The left maximum is OPERATIONAL state cost, not formation. -/
theorem channelCostSandwich {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (E : Superop (Fin a) (Fin b)) (hE : IsChannel E) :
    IsGreatest (stateCostOutputs E) (sSup (stateCostOutputs E)) ∧
      IsGreatest (formationOutputs E) (singleLetterCost E) ∧
      sSup (stateCostOutputs E) ≤ channelCost E ∧
      channelCost E ≤ (singleLetterCost E : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P41

end

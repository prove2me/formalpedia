-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_singleLetterAchievability
-- name    : QAlgorithms.Papers.Independent.Dependency50.P41.singleLetterAchievability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:49:34.070024+00:00
-- url     : https://prove2.me/theorems/3ec9e3c8-e0f0-4b3b-8c73-7bb951c013e9
-- title:
--   Single-letter formation achievability
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces of positive dimension. Logarithms and entropies are in bits. Let $\mathcal E:A\to B$ be CPTP and $A^\prime\cong A$. The channel cost $E_C(\mathcal E)$ is the infimum of asymptotic LOCC simulation rates: Alice initially holds the entire input and one half of a normalized maximally entangled state of Schmidt rank $M_n$, Bob holds the other half, Alice has no required output, and Bob receives the output. One protocol at each block length approximates the whole channel $\mathcal E^{\otimes n}$ in full diamond norm, with error tending to zero; its rate is $\limsup_n\log_2 M_n/n$. For a normalized bipartite state $\omega$, $E_F(\omega)$ is the infimum of the average marginal von Neumann entropy over normalized pure-state probability ensembles representing $\omega$. The following maximum over every normalized pure input is attained: $$E_C(\mathcal E)\le E_C^1(\mathcal E):=\max_{\psi\in\mathcal V(AA^\prime)}E_F\bigl((\mathcal E\otimes I_{A^\prime})(\psi)\bigr).$$
--
--   This gives an unregularized upper bound; it asserts no equality between operational cost and the single-letter quantity.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, PDF p. 9, Lemma 14

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

/-- arXiv:1108.5357v3, PDF pp.9–11, Lemma 14, (38). -/
theorem singleLetterAchievability {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (E : Superop (Fin a) (Fin b)) (hE : IsChannel E) :
    IsGreatest (formationOutputs E) (singleLetterCost E) ∧
      channelCost E ≤ (singleLetterCost E : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P41

end

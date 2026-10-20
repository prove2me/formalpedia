-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_regularizedConverse
-- name    : QAlgorithms.Papers.Independent.Dependency50.P41.regularizedConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:51:24.52144+00:00
-- url     : https://prove2.me/theorems/36f54391-55c1-42a0-aa5d-5debb70a4047
-- title:
--   Operational converse for channel simulation
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces of positive dimension. Logarithms and entropies are in bits. Let $\mathcal E:A\to B$ be CPTP. The channel cost $E_C(\mathcal E)$ is the infimum of asymptotic LOCC simulation rates: Alice initially holds the entire input and one half of a normalized maximally entangled state of Schmidt rank $M_n$, Bob holds the other half, Alice has no required output, and Bob receives the output. One protocol at each block length approximates the whole channel $\mathcal E^{\otimes n}$ in full diamond norm, with error tending to zero; its rate is $\limsup_n\log_2 M_n/n$. For a normalized bipartite state $\omega$, $E_F(\omega)$ is the infimum of the average marginal von Neumann entropy over normalized pure-state probability ensembles representing $\omega$. For each $n\ge1$, let $A_n=A^{\otimes n}$ and let $A_n^\prime$ be a full copy of $A_n$. Define the attained maximum $$F_n=\max_{\psi\in\mathcal V(A_nA_n^\prime)}E_F\bigl((\mathcal E^{\otimes n}\otimes I_{A_n^\prime})(\psi)\bigr),$$ where $\mathcal V$ contains all normalized pure states, with no product-input restriction. The ordinary real limit exists and $$E_C(\mathcal E)\ge\lim_{n\to\infty}\frac{F_n}{n}.$$
--
--   This bounds every asymptotically faithful simulation from below, without assuming an intermediate proof-generated state inequality.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, PDF p. 11, Proposition 16

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

/-- arXiv:1108.5357v3, PDF pp.11–12, Proposition 16, (57). -/
theorem regularizedConverse {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (E : Superop (Fin a) (Fin b)) (hE : IsChannel E) :
    blockMaxima E ∧ ∃ L : ℝ,
      Tendsto (fun n : ℕ => singleLetterCost (blockChannel E n) / (n : ℝ)) atTop (nhds L) ∧
      (L : EReal) ≤ channelCost E := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P41

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_channelEntanglementCost
-- name    : QAlgorithms.Papers.Independent.Dependency50.P41.channelEntanglementCost
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:47:57.321465+00:00
-- url     : https://prove2.me/theorems/46c7d144-d663-4f70-a209-f24596a4f5ac
-- title:
--   Operational channel entanglement cost equals regularized maximum formation
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces of positive dimension. Logarithms and entropies are in bits. Let $\mathcal E:A\to B$ be CPTP. The channel cost $E_C(\mathcal E)$ is the infimum of asymptotic LOCC simulation rates: Alice initially holds the entire input and one half of a normalized maximally entangled state of Schmidt rank $M_n$, Bob holds the other half, Alice has no required output, and Bob receives the output. One protocol at each block length approximates the whole channel $\mathcal E^{\otimes n}$ in full diamond norm, with error tending to zero; its rate is $\limsup_n\log_2 M_n/n$. For a normalized bipartite state $\omega$, $E_F(\omega)$ is the infimum of the average marginal von Neumann entropy over normalized pure-state probability ensembles representing $\omega$. For each $n\ge1$, let $A_n=A^{\otimes n}$ and let $A_n^\prime$ be a full copy of $A_n$. Define the attained maximum $$F_n=\max_{\psi\in\mathcal V(A_nA_n^\prime)}E_F\bigl((\mathcal E^{\otimes n}\otimes I_{A_n^\prime})(\psi)\bigr),$$ where $\mathcal V$ contains all normalized pure states, with no product-input restriction. The ordinary real limit exists and $$E_C(\mathcal E)=\lim_{n\to\infty}\frac{F_n}{n}.$$
--
--   This characterizes the operational parallel simulation cost; it does not define that cost by the entropy expression.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, PDF p. 7, Theorem 12 (Eq.22; paper-result seed)

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

/-- arXiv:1108.5357v3, PDF p.7, Theorem 12, (22); seed on pp.1–2.
The printed equality to V is read as membership, as in Propositions 15–16. -/
theorem channelEntanglementCost {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (E : Superop (Fin a) (Fin b)) (hE : IsChannel E) :
    blockMaxima E ∧ ∃ L : ℝ,
      Tendsto (fun n : ℕ => singleLetterCost (blockChannel E n) / (n : ℝ)) atTop (nhds L) ∧
      channelCost E = (L : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P41

end

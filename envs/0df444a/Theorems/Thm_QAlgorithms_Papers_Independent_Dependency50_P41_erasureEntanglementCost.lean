-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_erasureEntanglementCost
-- name    : QAlgorithms.Papers.Independent.Dependency50.P41.erasureEntanglementCost
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:54:43.944575+00:00
-- url     : https://prove2.me/theorems/cc2a5ab2-ad3d-4b70-82f1-dfc3b0ef9336
-- title:
--   Operational entanglement cost of the qubit erasure channel
-- statement:
--   For $0\le p\le1$, let $\mathcal E_{\mathrm{eras}}$ be the channel from a qubit to a qutrit defined on every operator by $\mathcal E_{\mathrm{eras}}(X)=(1-p)JXJ^\dagger+p\operatorname{tr}(X)|e\rangle\langle e|$, where $J$ embeds the qubit into the first two output basis vectors and $|e\rangle$ is the orthogonal third basis vector. The channel cost $E_C(\mathcal E)$ is the infimum of asymptotic LOCC simulation rates: Alice initially holds the entire input and one half of a normalized maximally entangled state of Schmidt rank $M_n$, Bob holds the other half, Alice has no required output, and Bob receives the output. One protocol at each block length approximates the whole channel $\mathcal E^{\otimes n}$ in full diamond norm, with error tending to zero; its rate is $\limsup_n\log_2 M_n/n$. Then $$E_C(\mathcal E_{\mathrm{eras}})=1-p.$$
--
--   This is the explicit entanglement-cost equality in (93)–(95), credited in the source to [53]; no capacity or strong-converse assertion is included.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, PDF p. 18, Unnumbered worked result, Eqs.(93)–(95): qubit erasure cost

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

/-- arXiv:1108.5357v3, PDF p.18, (93)–(95), credited there to [53]. -/
theorem erasureEntanglementCost (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    channelCost (qubitErasure p) = ((1 - p : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P41

end

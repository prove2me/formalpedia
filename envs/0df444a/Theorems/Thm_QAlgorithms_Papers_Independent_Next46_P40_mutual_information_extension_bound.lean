-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P40_mutual_information_extension_bound
-- name    : QAlgorithms.Papers.Independent.Next46.P40.mutual_information_extension_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:52:47.022219+00:00
-- url     : https://prove2.me/theorems/db687e7b-e099-4f70-b441-db862f82d7e7
-- title:
--   Mutual information bounded using an extension
-- statement:
--   Let $\sigma^{ABE}$ be any density operator on finite nonzero registers. The state may be mixed. With all entropies in bits and all marginals taken from $\sigma$,
--
--   $$I(A;B)_\sigma\le H(B)_\sigma+H(B\mid E)_\sigma.$$
--
--   Here $I(A;B)=H(A)+H(B)-H(AB)$ and $H(B\mid E)=H(BE)-H(E)$. The bound allows an extension of a state to control its mutual information without assuming that extension is pure.
-- source:
--   Entanglement-Assisted Capacity of Quantum Multiple-Access Channels, arXiv:quant-ph/0511228v2, PDF p. 4, Lemma 4, (24)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Next46.P40

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation marginalRB associate)

variable {A B C E R S : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype R] [Fintype S]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E]

variable [DecidableEq R] [DecidableEq S]

/-- PDF p.4, Lemma 4: no purity assumption on sigma, and no separately
postulated purifying reference or entropy inequality. -/
theorem mutual_information_extension_bound
    [Nonempty A] [Nonempty B] [Nonempty E]
    (sigma : Matrix ((A × B) × E) ((A × B) × E) ℂ)
    (hsigma : IsDensityMatrix sigma) :
    mutualInformation (traceRight sigma) ≤
      vnEntropy (traceLeft (traceRight sigma)) +
      (vnEntropy (marginalBC sigma) - vnEntropy (traceLeft sigma)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P40

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P06_eb_two_block_information
-- name    : QAlgorithms.Papers.Independent.Frontier30.P06.eb_two_block_information
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:27:24.926569+00:00
-- url     : https://prove2.me/theorems/0070ecae-cec0-4a12-9298-956a4dd825bf
-- title:
--   Entanglement-breaking two-block information bounds
-- statement:
--   Consider a legal executed two-block classical-feedback protocol with any normalized prior over $M\ge1$ messages. The first block $\Omega$ is entanglement-breaking and the second block $\Lambda$ is any positive finite-dimensional completely positive trace-preserving channel. Alice and Bob start without shared entanglement; arbitrary entangled sender inputs are allowed. Let $B_1$ denote all receiver memory after the first feedback operation and let $B_2$ be the second channel output before subsequent local processing. Keep an untouched orthogonal message reference $M$. The joint state on these registers is the one computed by executing this same protocol.
--
--   Write $B_{\mathrm f}$ for the final receiver memory and $\chi$ for the maximum single-block output Holevo information. In bits,
--
--   $$
--   I(MB_1:B_2)\le\chi(\Lambda),\qquad I(M:B_{\mathrm f})\le\chi(\Omega)+\chi(\Lambda).
--   $$
--
--   These finite information bounds underlie the feedback converse for entanglement-breaking channels. The first bound uses the full first-system entropy $S(MB_1)$ in the definition of mutual information.
--
--   **Formalization Note** Equation (24) prints $S(M)$ in that expansion; it is corrected to $S(MB_1)$, consistently with the left-hand side and the rest of the derivation.
-- source:
--   On Feedback and the Classical Capacity of a Noisy Quantum Channel, arXiv:quant-ph/0305176v1, PDF p. 4, (24)-(25)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Frontier30.P06

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (Backward tensorAction)

open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

/-- PDF p.4, equations (24)-(25): after an EB first block, the actual second
output has I(M B1:B2) <= chi(second), and total message information is bounded by
the two block maxima. The second block can be any channel. Typo correction:
(24) prints S(M); it must be S(M B1), as implemented in bipartiteInformation.
For constant M and independent fair bits B1,B2, the printed expansion is
-1, whereas the corrected mutual information is 0 bits; for correlated fair
bits it is 0 instead of the correct 1 bit. -/
theorem eb_two_block_information {ch : ℕ → Backward} {M : ℕ}
    (P : FeedbackExecution ch 2 M) (hP : P.Valid) (p : Fin M → ℝ) (hp : Prior p)
    (hEB : (ch 0).IsEB) :
    bipartiteInformation (P.splitReceived p 1) ≤ channelHolevo (ch 1).map ∧
      P.information p ≤ channelHolevo (ch 0).map + channelHolevo (ch 1).map := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P06

end

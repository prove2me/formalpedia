-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P14_fiveParty_subadditivity
-- name    : QAlgorithms.Papers.Independent.Gap20.P14.fiveParty_subadditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:30:27.308343+00:00
-- url     : https://prove2.me/theorems/9a3f1770-74b3-46d4-909d-22bd555382e4
-- title:
--   Five-party pure-state subadditivity of squashed entanglement
-- statement:
--   Let $A,B_1,E_1,B_2,E_2$ be positive finite-dimensional quantum registers and let $\lvert\psi\rangle_{AB_1E_1B_2E_2}$ be any unit vector. For a bipartite density operator, let $E_{\rm sq}$ denote half the infimum of conditional mutual information in bits over all extensions, equivalently over all squashing channels of a purification. Taking all the following states as reductions and groupings of this same pure state gives
--
--   $$
--   E_{\rm sq}(A;B_1B_2)_\psi\le E_{\rm sq}(AB_2E_2;B_1)_\psi+E_{\rm sq}(AB_1E_1;B_2)_\psi.
--   $$
--
--   This is the subadditivity inequality used to bound the entanglement added by individual channel uses. The environments may be correlated; neither side assumes a product state or an optimal squashing map.
-- source:
--   Fundamental rate-loss tradeoff for optical quantum key distribution, arXiv:1504.06390v1, PDF p. 4, Lemma 2: five-party pure-state subadditivity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P14

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Claimed50.P12 (squashedEntanglement)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1504.06390v1, PDF p.4, Lemma 2, restated and proved on p.10:
five-party subadditivity for one arbitrary normalized pure state.
No independence, optimal-squasher, or factorization assumption is imposed.
All systems are positive finite dimensional as in the source's Methods setting. -/
theorem fiveParty_subadditivity
    {A B1 E1 B2 E2 : Type}
    [Fintype A] [Fintype B1] [Fintype E1] [Fintype B2] [Fintype E2]
    [Nonempty A] [Nonempty B1] [Nonempty E1] [Nonempty B2] [Nonempty E2]
    (psi : EuclideanSpace ℂ (FiveBasis A B1 E1 B2 E2)) (hpsi : ‖psi‖ = 1) :
    squashedEntanglement (honestReduction (pureDensity psi)) ≤
      squashedEntanglement (firstLinkReduction (pureDensity psi)) +
      squashedEntanglement (secondLinkReduction (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P14

end

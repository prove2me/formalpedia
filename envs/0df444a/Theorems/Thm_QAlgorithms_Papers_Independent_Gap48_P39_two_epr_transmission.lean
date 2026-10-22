-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_two_epr_transmission
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.two_epr_transmission
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:23:19.984715+00:00
-- url     : https://prove2.me/theorems/4d028c6a-67e3-4435-bbc7-ca0396f23ba0
-- title:
--   Unnumbered strengthening of Theorem 8: independent entanglement transmission
-- statement:
--   Let $\mathcal N:A'\to BC$ be any finite-dimensional CPTP broadcast channel on positive-dimensional systems, and let $|\psi\rangle^{A_BA_CA'}$ be a unit pure state, with $A_B,A_C$ retained local reference factors that may be correlated. Put $\sigma=(\mathrm{id}_{A_BA_C}\otimes\mathcal N)(\psi)$. If both coherent informations below are positive, then
--
--   $$\bigl(I(A_B\rangle B)_\sigma,\ I(A_C\rangle C)_\sigma\bigr)\in\mathcal E_{\mathrm{trans}}(\mathcal N).$$
--
--   Entropies are in bits. The transmission region is independently defined: Alice receives the sender halves of two independent EPR pairs, leaves their external reference halves untouched, applies a CPTP encoder into the block channel inputs, and Bob and Charlie decode locally. A single joint squared-fidelity test compares the result with the independent EPR product. The region is the closure of nonnegative floor-exponential-rank rates with vanishing error and no side communication or preshared assistance. This is transmission of supplied entanglement, distinct from freely preparing the reference/input state of a generation code.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 13, Unnumbered strengthening of Theorem 8: independent entanglement transmission

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P39

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Gap48.P39

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks holevoInfo)

open QAlgorithms.Papers.Independent.Dependency50.P19 (both epr mutualInformation marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity conditionalEntropy groupedChannelPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C X T E : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X]

variable [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]

/-- Unnumbered strengthening of Theorem 8, PDF p.13: independent two-EPR
TRANSMISSION at the same coherent-information rates, with fixed external references. -/
theorem two_epr_transmission [Nonempty A] [Nonempty B] [Nonempty C]
    {AB AC : Type} [Fintype AB] [Fintype AC] [DecidableEq AB] [DecidableEq AC]
    [Nonempty AB] [Nonempty AC] (N : Superop A (B × C)) (hN : IsChannel N)
    (psi : EuclideanSpace ℂ ((AB × AC) × A)) (hp : IsState psi)
    (hB : 0 < (twoEprInformation N psi).1) (hC : 0 < (twoEprInformation N psi).2) :
    twoEprInformation N psi ∈ twoEprTransmissionCapacity N := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end

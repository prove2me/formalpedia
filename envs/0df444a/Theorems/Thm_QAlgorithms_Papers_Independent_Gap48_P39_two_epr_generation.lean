-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P39_two_epr_generation
-- name    : QAlgorithms.Papers.Independent.Gap48.P39.two_epr_generation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:22:30.500412+00:00
-- url     : https://prove2.me/theorems/05e28cd0-28e8-42f8-acb3-a63addf01933
-- title:
--   Theorem 8: unassisted simultaneous bipartite entanglement generation
-- statement:
--   Let $\mathcal N:A'\to BC$ be a finite-dimensional CPTP channel, and let $|\psi\rangle^{A_BA_CA'}$ be a unit pure state on positive-dimensional systems. The systems $A_B,A_C$ are retained locally by Alice; their joint state need not factor. Put $\sigma=(\mathrm{id}_{A_BA_C}\otimes\mathcal N)(\psi)$ and compute both marginal coherent informations in bits. If both are strictly positive, then
--
--   $$\bigl(I(A_B\rangle B)_\sigma,\ I(A_C\rangle C)_\sigma\bigr)\in\mathcal E_{\mathrm{gen}}(\mathcal N).$$
--
--   Here $\mathcal E_{\mathrm{gen}}$ is the closed unassisted two-EPR generation region. Its codes have one joint pure block preparation with locally retained references and separate receiver CPTP decoders, and are tested by a single squared-fidelity criterion against the product of independent Alice–Bob and Alice–Charlie EPR states. Ranks follow $\lfloor2^{nR}\rfloor$, errors vanish, and there is no initial shared entanglement or final side communication. This generates the two computed resources simultaneously, rather than a GHZ/EPR pair.
-- source:
--   Quantum broadcast channels, arXiv:quant-ph/0603098v2, PDF p. 13, Theorem 8: unassisted simultaneous bipartite entanglement generation

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

/-- Theorem 8, PDF p.13: both positive coherent informations achievable
simultaneously, with independent final EPRs. Alice's reference factors need not be independent. -/
theorem two_epr_generation [Nonempty A] [Nonempty B] [Nonempty C]
    {AB AC : Type} [Fintype AB] [Fintype AC] [DecidableEq AB] [DecidableEq AC]
    [Nonempty AB] [Nonempty AC] (N : Superop A (B × C)) (hN : IsChannel N)
    (psi : EuclideanSpace ℂ ((AB × AC) × A)) (hp : IsState psi)
    (hB : 0 < (twoEprInformation N psi).1) (hC : 0 < (twoEprInformation N psi).2) :
    twoEprInformation N psi ∈ twoEprCapacity N := by sorry

end QAlgorithms.Papers.Independent.Gap48.P39

end

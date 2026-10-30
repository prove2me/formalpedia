-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P38_erasureAverageUpper
-- name    : QAlgorithms.Papers.Independent.Bridge50.P38.erasureAverageUpper
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:43:31.16826+00:00
-- url     : https://prove2.me/theorems/08dabc69-b051-49e8-a971-a8a9c8479dea
-- title:
--   Bounded average-fidelity capacity below the erasure threshold
-- statement:
--   All systems are nonempty finite-dimensional complex Hilbert spaces. The channel $\mathcal N:A\to B$ is completely positive and trace preserving, and its $n$ uses are independent. A code embeds a positive integer dimensional subspace of $A^{\otimes n}$ and uses a CPTP decoder into that ambient input space. Write $Q^{n,\varepsilon}$ for the supremum of $\log_2 m$ over codes with Haar-average squared pure-state fidelity at least $1-\varepsilon$, and $Q_{\rm et}^{n,\varepsilon}$ for the corresponding maximally entangled squared-overlap criterion. These are total qubits per block.
--
--   Let $\mathcal E_{1/2}$ be the symmetric erasure channel with any positive finite input dimension and one orthogonal pure erasure flag. For each fixed $0<\varepsilon<1/2$ there is a constant $K>0$, chosen before $n$, such that
--
--   $$Q^{n,\varepsilon}(\mathcal E_{1/2})\le K\qquad\text{for every }n\ge1.$$
--
--   This is the introduction's average-fidelity capacity assertion. It does not assign to it the explicit same-error constant established in Section 4 for entanglement fidelity.
-- source:
--   Decoding quantum information via the Petz recovery map, arXiv:1504.04449v4, PDF p. 2, erasure-average-upper

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Bridge50.P38

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Information100.P63 (normalQuantile)

open QAlgorithms.Papers.Independent.Dependency50.P36
  (relativeEntropyFinite pairInformationVariance)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (columnProjector pinch marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification singleUseInformation coherentInformation)

open QAlgorithms.Papers.Independent.Gap48.P23 (CompletelyPositive)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- PDF p.2, Section 1.1: average-fidelity capacity stays bounded at fixed
error below one half. This does not claim the same explicit constant as for Q_et. -/
theorem erasureAverageUpper [Nonempty A]
    (epsilon : ℝ) (he0 : 0 < epsilon) (hehalf : epsilon < 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      averageCapacity (symmetricErasure A) n epsilon ≤ (K : EReal) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P38

end

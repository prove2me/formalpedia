-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P38_entanglementCapacityLeAverage
-- name    : QAlgorithms.Papers.Independent.Bridge50.P38.entanglementCapacityLeAverage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:40:34.450908+00:00
-- url     : https://prove2.me/theorems/9ffea03a-c087-42cb-b0a4-a71cab510c6f
-- title:
--   Entanglement transmission is bounded by average transmission capacity
-- statement:
--   All systems are nonempty finite-dimensional complex Hilbert spaces. The channel $\mathcal N:A\to B$ is completely positive and trace preserving, and its $n$ uses are independent. A code embeds a positive integer dimensional subspace of $A^{\otimes n}$ and uses a CPTP decoder into that ambient input space. Write $Q^{n,\varepsilon}$ for the supremum of $\log_2 m$ over codes with Haar-average squared pure-state fidelity at least $1-\varepsilon$, and $Q_{\rm et}^{n,\varepsilon}$ for the corresponding maximally entangled squared-overlap criterion. These are total qubits per block.
--
--   For every $n\ge1$ and $0\le\varepsilon<1$,
--
--   $$Q^{n,\varepsilon}(\mathcal N)\ge Q_{\rm et}^{n,\varepsilon}(\mathcal N).$$
--
--   The error, block length, subspace encoder class and ambient decoder class are identical on the two sides. This is the operational comparison, rather than an equality of fidelities for arbitrary ambient decoders.
-- source:
--   Decoding quantum information via the Petz recovery map, arXiv:1504.04449v4, PDF p. 8, eq-3.7

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

/-- PDF pp.7–8, (3.7): operational comparison at the same n and epsilon.
No false ambient-decoder equality of average and entanglement fidelity is asserted. -/
theorem entanglementCapacityLeAverage [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (n : ℕ) (hn : 1 ≤ n)
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon < 1) :
    subspaceCapacity true N n epsilon ≤ averageCapacity N n epsilon := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P38

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P38_erasureSquareRootLower
-- name    : QAlgorithms.Papers.Independent.Bridge50.P38.erasureSquareRootLower
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:44:27.278181+00:00
-- url     : https://prove2.me/theorems/f8d2ac19-43d7-4551-837e-b8a4f2fcf4b6
-- title:
--   Positive second-order erasure achievability above one half
-- statement:
--   All systems are nonempty finite-dimensional complex Hilbert spaces. The channel $\mathcal N:A\to B$ is completely positive and trace preserving, and its $n$ uses are independent. A code embeds a positive integer dimensional subspace of $A^{\otimes n}$ and uses a CPTP decoder into that ambient input space. Write $Q^{n,\varepsilon}$ for the supremum of $\log_2 m$ over codes with Haar-average squared pure-state fidelity at least $1-\varepsilon$, and $Q_{\rm et}^{n,\varepsilon}$ for the corresponding maximally entangled squared-overlap criterion. These are total qubits per block.
--
--   Let $\mathcal E_{1/2}$ be the symmetric erasure channel on an input of dimension $d\ge2$, and fix $1/2<\varepsilon<1$. With coherent information and maximizing-input dispersion as in Definition 2.8,
--
--   $$I_c(\mathcal E_{1/2})=0,\qquad V_\varepsilon(\mathcal E_{1/2})>0.$$
--
--   There exist $K>0$ and $n_0\ge2$, fixed before $n$, such that
--
--   $$Q^{n,\varepsilon}(\mathcal E_{1/2})\ge Q_{\rm et}^{n,\varepsilon}(\mathcal E_{1/2})\ge\sqrt{nV_\varepsilon(\mathcal E_{1/2})}\,\Phi^{-1}(\varepsilon)-K\log_2n\qquad(n\ge n_0).$$
--
--   The capacity comparison holds for all $n\ge1$. Consequently there exist $c>0$ and $n_1\ge2$ with $Q_{\rm et}^{n,\varepsilon}(\mathcal E_{1/2})\ge c\sqrt n>0$ for every $n\ge n_1$. This is an eventual lower bound and asserts no matching upper bound.
-- source:
--   Decoding quantum information via the Petz recovery map, arXiv:1504.04449v4, PDF p. 21, erasure-lower

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

/-- PDF pp.20–21, Section 4 (and p.2): eventual positive sqrt(n) lower bound.
Printed: Section 4 asserts strictly positive dispersion without qualifying input dimension.
Changed: require nontrivial input (dimension at least two) for this strict lower bound.
Why: in dimension one both capacity and variance vanish; at the maximally mixed input
in dimension d>=2, variance is (log2 d)^2>0. No matching upper bound is claimed. -/
theorem erasureSquareRootLower [Nontrivial A]
    (epsilon : ℝ) (hehalf : 1/2 < epsilon) (he1 : epsilon < 1) :
    singleUseInformation (symmetricErasure A) = 0 ∧
    0 < quantumDispersion (symmetricErasure A) epsilon (ne_of_gt hehalf) ∧
    (∀ n : ℕ, 1 ≤ n →
      subspaceCapacity true (symmetricErasure A) n epsilon ≤
        averageCapacity (symmetricErasure A) n epsilon) ∧
    (∃ K : ℝ, 0 < K ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0,
      ((secondOrderCorrection (symmetricErasure A) epsilon n - K * log2 n : ℝ) : EReal) ≤
        subspaceCapacity true (symmetricErasure A) n epsilon) ∧
    ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0,
      ((c * Real.sqrt n : ℝ) : EReal) ≤
        subspaceCapacity true (symmetricErasure A) n epsilon := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P38

end

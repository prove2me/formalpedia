-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P38_erasureEntanglementUpper
-- name    : QAlgorithms.Papers.Independent.Bridge50.P38.erasureEntanglementUpper
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:42:35.414215+00:00
-- url     : https://prove2.me/theorems/6d989e1b-e4d6-4a56-86d6-47dfec475d6a
-- title:
--   Finite-block entanglement upper bound for symmetric erasure
-- statement:
--   All systems are nonempty finite-dimensional complex Hilbert spaces. The channel $\mathcal N:A\to B$ is completely positive and trace preserving, and its $n$ uses are independent. A code embeds a positive integer dimensional subspace of $A^{\otimes n}$ and uses a CPTP decoder into that ambient input space. Write $Q^{n,\varepsilon}$ for the supremum of $\log_2 m$ over codes with Haar-average squared pure-state fidelity at least $1-\varepsilon$, and $Q_{\rm et}^{n,\varepsilon}$ for the corresponding maximally entangled squared-overlap criterion. These are total qubits per block.
--
--   Let $A$ have any positive finite dimension and let $\mathcal E_{1/2}(X)=\tfrac12X\oplus\tfrac12\operatorname{tr}(X)|e\rangle\langle e|$, with the flag orthogonal to $A$. For every $n\ge1$ and $0<\varepsilon<1/2$,
--
--   $$Q_{\rm et}^{n,\varepsilon}(\mathcal E_{1/2})\le\log_2\frac1{1-2\varepsilon}.$$
--
--   This is a uniform finite-block bound, equal to the source's $\log_2(1/\cos(2\alpha))$ with $\sin\alpha=\sqrt\varepsilon$ and $0<\alpha<\pi/4$. It includes the dimension-one input case.
-- source:
--   Decoding quantum information via the Petz recovery map, arXiv:1504.04449v4, PDF p. 21, erasure-ent-upper

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

/-- PDF pp.20–21, Section 4: finite-block uniform upper bound for the
50-50 erasure channel; cos(2 alpha)=1-2 epsilon>0. Includes dimension one. -/
theorem erasureEntanglementUpper [Nonempty A] (n : ℕ) (hn : 1 ≤ n)
    (epsilon : ℝ) (he0 : 0 < epsilon) (hehalf : epsilon < 1/2) :
    subspaceCapacity true (symmetricErasure A) n epsilon ≤
      (log2 (1 / (1 - 2 * epsilon)) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P38

end

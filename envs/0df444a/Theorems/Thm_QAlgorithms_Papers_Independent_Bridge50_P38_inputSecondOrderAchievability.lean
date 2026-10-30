-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P38_inputSecondOrderAchievability
-- name    : QAlgorithms.Papers.Independent.Bridge50.P38.inputSecondOrderAchievability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:41:36.130013+00:00
-- url     : https://prove2.me/theorems/07dccd50-102d-4ed5-8d3b-efecdb2b271a
-- title:
--   Second-order achievability for every fixed density input
-- statement:
--   All systems are nonempty finite-dimensional complex Hilbert spaces. The channel $\mathcal N:A\to B$ is completely positive and trace preserving, and its $n$ uses are independent. A code embeds a positive integer dimensional subspace of $A^{\otimes n}$ and uses a CPTP decoder into that ambient input space. Write $Q^{n,\varepsilon}$ for the supremum of $\log_2 m$ over codes with Haar-average squared pure-state fidelity at least $1-\varepsilon$, and $Q_{\rm et}^{n,\varepsilon}$ for the corresponding maximally entangled squared-overlap criterion. These are total qubits per block.
--
--   Fix any density input $\rho$ and $0<\varepsilon<1$. Let $\Psi^\rho_{RA}$ purify $\rho$, put $\omega_{RB}=(\operatorname{id}_R\otimes\mathcal N)(\Psi^\rho)$, and define $D_\rho=D(\omega_{RB}\|I_R\otimes\omega_B)$ and $V_\rho=V(\omega_{RB}\|I_R\otimes\omega_B)$ using binary logarithms. There exist $K>0$ and $n_0\ge2$, depending on the fixed channel, input and error but chosen before $n$, such that
--
--   $$Q_{\rm et}^{n,\varepsilon}(\mathcal N)\ge nD_\rho+\sqrt{nV_\rho}\,\Phi^{-1}(\varepsilon)-K\log_2n\qquad(n\ge n_0).$$
--
--   Pure inputs, zero variance, and uncorrelated environments remain included. The result retains the source's input-dependent claim without assuming a strict entropy gap from its proof.
-- source:
--   Decoding quantum information via the Petz recovery map, arXiv:1504.04449v4, PDF p. 19, eq-3.25

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

/-- PDF p.19, (3.25): arbitrary fixed input, including pure input and zero
variance. Constants may depend on this input, channel, and error, but not on n.
The proof's strict entropy-gap claim is not added as a hypothesis. -/
theorem inputSecondOrderAchievability [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N)
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho)
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    ∃ K : ℝ, 0 < K ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0,
      (((n : ℝ) * coherentInformation N rho +
        Real.sqrt ((n : ℝ) * inputVariance N rho) * normalQuantile epsilon -
        K * log2 n : ℝ) : EReal) ≤ subspaceCapacity true N n epsilon := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P38

end

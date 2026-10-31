-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_uniform_classical_representation
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.uniform_classical_representation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:27:56.108625+00:00
-- url     : https://prove2.me/theorems/5ebccf86-69c1-4a1f-90f6-a0fba8083770
-- title:
--   Proposition 8: Uniform asymptotic classical representation
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. For a state $\rho_{AB}$ and a positive reference $\tau_A$ covering $\rho_A$, write $I_\alpha(\rho\|\tau)=\inf_{\sigma_B\in\mathcal S(B)}D_\alpha(\rho\|\tau\otimes\sigma_B)$ and $\widetilde I_\alpha$ for the analogous sandwiched quantity. Fix states $\rho_{AB},\tau_A$ with $\rho_A\ll\tau_A$, and the specific universal state $\omega_n$ from (2.7). Put $K_n=\tau_A^{\otimes n}\otimes\omega_n$ and $L_n=\mathcal P_{K_n}(\rho_{AB}^{\otimes n})$. There exist $C>0$ and $N\ge2$, depending on $\rho,\tau$ and the fixed dimensions, such that for every $n\ge N$ and every finite $\alpha\ge1/2$,
--   $$\left|\frac1nD_\alpha(L_n\|K_n)-\widetilde I_\alpha(\rho\|\tau)\right|\le C\frac{\log n}{n}.$$
--   The constant and threshold are independent of the order. Both quantities are finite under these hypotheses. This uniform approximation is strong enough to retain second-order asymptotics.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 10, Proposition 8: Uniform asymptotic classical representation

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P47

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Topology

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P28 (SupportLE pinch logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

open QAlgorithms.Papers.Independent.Claimed50.P12 (DiagonalIn)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D I J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq I] [DecidableEq J]

/-- arXiv:1408.6894v5, PDF pp.10--11, Proposition 8, (3.18).
The absolute error constant and threshold precede alpha and are uniform over it.
The proof's erroneous plus in (3.25) is not asserted. -/
theorem uniform_classical_representation [Nonempty A] (d : ℕ) (hd : 0 < d)
    (rho : Op (A × Fin d)) (tau : Op A) (hr : IsDensityMatrix rho)
    (ht : IsDensityMatrix tau) (hS : SupportLE (traceRight rho) tau) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N, ∀ a : ℝ, 1/2 ≤ a →
      |(completedRenyiDivergence false (a : RenyiOrder) (classicalNull n rho tau) (universalReference n tau)).toReal / n -
        (generalizedInformation true (a : RenyiOrder) rho tau).toReal| ≤ K * Real.log n / n := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_local_order_expansion
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.local_order_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:28:52.648776+00:00
-- url     : https://prove2.me/theorems/96b509a1-6ac4-4e0d-b6da-a840b5bbb093
-- title:
--   Corollary 9: Local-order second-order pinching expansion
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. For a state $\rho_{AB}$ and a positive reference $\tau_A$ covering $\rho_A$, write $I_\alpha(\rho\|\tau)=\inf_{\sigma_B\in\mathcal S(B)}D_\alpha(\rho\|\tau\otimes\sigma_B)$ and $\widetilde I_\alpha$ for the analogous sandwiched quantity. Fix states $\rho_{AB},\tau_A$ with $\rho_A\ll\tau_A$. Use $K_n=\tau_A^{\otimes n}\otimes\omega_n$ and $L_n=\mathcal P_{K_n}(\rho_{AB}^{\otimes n})$. Write $I= D(\rho_{AB}\|\tau_A\otimes\rho_B)$ and
--   $$V=\operatorname{tr}\rho_{AB}\bigl(\log\rho_{AB}-\log(\tau_A\otimes\rho_B)-I\,1\bigr)^2.$$
--   For every real $t$, the order $1+t/\sqrt n$ is eventually at least $1/2$, and
--   $$\lim_{n\to\infty}\frac{t}{\sqrt n}\left[D_{1+t/\sqrt n}(L_n\|K_n)-nI\right]=\frac{t^2}{2}V.$$
--   The entire bracket is scaled by $t/\sqrt n$. At $t=0$ the limit is zero. This is the local-order expansion needed for fluctuation asymptotics.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 11, Corollary 9: Local-order second-order pinching expansion

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

/-- arXiv:1408.6894v5, PDF p.11, Corollary 9, (3.26).
The ENTIRE parenthesis is multiplied by t/sqrt(n). Positive copy counts are k+1;
negative t is admissible because its order lies in the source domain eventually. -/
theorem local_order_expansion [Nonempty A] (d : ℕ) (hd : 0 < d)
    (rho : Op (A × Fin d)) (tau : Op A) (hr : IsDensityMatrix rho)
    (ht : IsDensityMatrix tau) (hS : SupportLE (traceRight rho) tau) (t : ℝ) :
    (∀ᶠ k : ℕ in atTop, (1/2 : ℝ) ≤ 1 + t / Real.sqrt (k+1)) ∧
    Tendsto (fun k : ℕ => t / Real.sqrt (k+1) *
      ((completedRenyiDivergence false ((1 + t / Real.sqrt (k+1) : ℝ) : RenyiOrder)
        (classicalNull (k+1) rho tau) (universalReference (k+1) tau)).toReal -
        (k+1 : ℝ) * (informationOne rho tau).toReal))
      atTop (𝓝 (t^2 / 2 * generalizedInformationVariance rho tau)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end

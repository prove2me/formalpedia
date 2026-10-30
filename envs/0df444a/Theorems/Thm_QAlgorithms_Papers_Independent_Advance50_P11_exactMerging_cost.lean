-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_exactMerging_cost
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.exactMerging_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:36:46.66399+00:00
-- url     : https://prove2.me/theorems/6f806452-a09d-4157-9e48-6407f766e3d4
-- title:
--   Entanglement-cost converse for exact merging
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. A merging protocol is an actual adaptive finite LOCC map, with free classical communication, from Alice and Bob to the prescribed output registers. It acts as the identity on the inaccessible reference $R$. Its input is $\lvert\psi\rangle_{ABR}\otimes\lvert\Phi_K\rangle_{A_0B_0}$ and its full ideal output is $\lvert\psi\rangle_{B^{\prime}BR}\otimes\lvert\Phi_L\rangle_{A_1B_1}$, where $B^{\prime}$ is a fixed copy of $A$ and $K,L$ are positive natural Schmidt ranks. Its error is the full trace norm of actual output minus that entire pure target; its signed cost is $\log_2K-\log_2L$. For every normalized pure $\psi_{ABR}$ and every zero-error merging protocol,
--
--   $$
--   \log_2K-\log_2L\ge -H_{\min}(\rho_{AR}\mid\rho_R),
--   $$
--
--   where both marginals are computed from $\lvert\psi\rangle\langle\psi\rvert$.
--
--   This converse concerns perfect full-state reconstruction, with the actual marginal as reference.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 25, Proposition 4.10

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P11

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Support50.P21
  (conditionalMin conditionalMax hMin hMax largestEigenvalue)

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog supportRank tr)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC marginalAR)

open QAlgorithms.Papers.Independent.Information100.P22 (bell mixed)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 4.10, PDF p.25, (4.41): every exact physical LOCC merging process.
The hypothesis is the full zero-error target condition, not a branchwise decoupling premise. -/
theorem exactMerging_cost {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R] [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi) (K L : ℕ)
    (M : Superop ((A × Fin K) × (B × Fin K)) (Fin L × ((A × B) × Fin L)))
    (hmerge : Merges psi K L M 0) :
    -conditionalMin (marginalAR (pureDensity psi)) (traceRight (pureDensity psi)) ≤
      ((Real.logb 2 K - Real.logb 2 L : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end

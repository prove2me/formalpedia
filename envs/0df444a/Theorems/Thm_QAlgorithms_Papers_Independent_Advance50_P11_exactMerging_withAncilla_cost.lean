-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_exactMerging_withAncilla_cost
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.exactMerging_withAncilla_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:44:57.571974+00:00
-- url     : https://prove2.me/theorems/f6959b44-2f95-47f1-bd17-2e1fddac5546
-- title:
--   Exact merging converse with an independent Alice ancilla
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. A merging protocol is an actual adaptive finite LOCC map, with free classical communication, from Alice and Bob to the prescribed output registers. It acts as the identity on the inaccessible reference $R$. Its input is $\lvert\psi\rangle_{ABR}\otimes\lvert\Phi_K\rangle_{A_0B_0}$ and its full ideal output is $\lvert\psi\rangle_{B^{\prime}BR}\otimes\lvert\Phi_L\rangle_{A_1B_1}$, where $B^{\prime}$ is a fixed copy of $A$ and $K,L$ are positive natural Schmidt ranks. Its error is the full trace norm of actual output minus that entire pure target; its signed cost is $\log_2K-\log_2L$. In addition, Alice may receive any independent normalized ancillary density $\eta_C$, initially in tensor product with both $\psi_{ABR}$ and $\Phi_K$. For every zero-error LOCC merging protocol acting on this enlarged Alice input and producing the original full ideal target,
--
--   $$
--   \log_2K-\log_2L\ge-H_{\min}(\rho_{AR}\mid\rho_R).
--   $$
--
--   The original inaccessible reference $R$ and its actual marginal do not change.
--
--   The exact converse remains valid with private local ancillary randomness or quantum states.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 25, Remark 4.11

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

/-- Remark 4.11, PDF p.25: exact converse with any independent Alice input ancilla.
The source reference and the final whole target remain those of the original psi.
The ancillary density is normalized and is independent of both psi and Phi_K. -/
theorem exactMerging_withAncilla_cost {A B R C : Type}
    [Fintype A] [Fintype B] [Fintype R] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq R] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty R] [Nonempty C]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi)
    (eta : Matrix C C ℂ) (heta : IsDensityMatrix eta) (K L : ℕ) (hK : 0 < K) (hL : 0 < L)
    (M : Superop (((A × Fin K) × C) × (B × Fin K)) (Fin L × ((A × B) × Fin L)))
    (hlocc : IsLOCC M)
    (hexact : traceNorm (idTensorSuperop M (ancillaryInput psi eta K) -
      pureDensity (targetKet psi L)) ≤ 0) :
    -conditionalMin (marginalAR (pureDensity psi)) (traceRight (pureDensity psi)) ≤
      ((Real.logb 2 K - Real.logb 2 L : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end

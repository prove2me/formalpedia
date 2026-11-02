-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_moment_correlation_bound
-- name    : QuantumMaxCutEnergy.PauliSDP.moment_correlation_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T18:50:48.369552+00:00
-- url     : https://prove2.me/theorems/1b364783-8d90-4c82-939e-d24df1bc737c
-- title:
--   Level-2 correlation bound: $L(XX) + L(YY) + L(ZZ) \\le 1$ on one edge
-- statement:
--   The single-edge correlation bound of the level-2 Pauli-moment relaxation for Quantum Max-Cut.
--
--   Let $G$ have vertex set $\{1, \dots, n\}$ and let $L$ be a feasible solution of the level-$k$ Pauli-moment relaxation of the Quantum Max-Cut Hamiltonian, for some $k \ge 2$: the moment array $L$ assigns a real number to every Pauli word of support at most $k$, with $L(\mathbb 1) = 1$ and a positive semidefinite signed moment matrix. Write $L(X_i X_j)$, $L(Y_i Y_j)$, $L(Z_i Z_j)$ for the three two-body moments along a pair $i \ne j$. Then
--
--   $$L(X_iX_j) + L(Y_iY_j) + L(Z_iZ_j) \le 1 .$$
--
--   Equivalently, the per-edge expectation value $\tfrac12\bigl(1 - L(X_iX_j) - L(Y_iY_j) - L(Z_iZ_j)\bigr)$ is nonnegative.
--
--   **Role in the campaign.** In the notation of Lee and Parekh this states $v_i \cdot v_j \le \tfrac13$, the bound they use throughout the level-2 analysis of Quantum Max-Cut (ICALP 2024, Theorem 2). It is what caps the "positive excess" $h^+_{ij} = \max\bigl((3v_i\cdot v_j - 1)/4, 0\bigr)$ at $\tfrac12$ and makes the matching-state analysis well posed.
--
--   **Formalization Note.** The proof reads the four words $\{1, X_iX_j, Y_iY_j, Z_iZ_j\}$ off the signed moment Gram — a $4\times 4$ principal block with the phase structure of the Pauli algebra, whose off-diagonal signs are $+$ against the identity row and $-$ between distinct two-body words — and evaluates the quadratic form of positive semidefiniteness at the vector $(1, -1, -1, -1)$, which equals $4\bigl(1 - L(X_iX_j) - L(Y_iY_j) - L(Z_iZ_j)\bigr)$.
-- source:
--   Eunou Lee and Ojas Parekh, An Improved Quantum Max Cut Approximation via Matching, ICALP 2024, https://arxiv.org/abs/2401.03616 , proof of Theorem 2 (the bound $-1 \le v_i \cdot v_j \le 1/3$ on level-2 SDP solutions)

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.PauliSDP.moment_correlation_bound {n k : ℕ} (hk : 2 ≤ k)
    (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ)
    (hL : QuantumMaxCutEnergy.PauliSDP.Feasible k L)
    (i j : Fin n) (hij : i ≠ j) :
    L (fun t => if t = i ∨ t = j then 1 else 0) +
        L (fun t => if t = i ∨ t = j then 2 else 0) +
        L (fun t => if t = i ∨ t = j then 3 else 0) ≤ 1 := by sorry

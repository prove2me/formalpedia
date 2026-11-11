-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_full_level_exact
-- name    : QuantumMaxCutEnergy.PauliSDP.full_level_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:10:39.175537+00:00
-- url     : https://prove2.me/theorems/7d30fe08-e62b-42d1-ae68-8ca32211e857
-- title:
--   The Pauli moment relaxation on $n$ qubits is exact at level $n$
-- statement:
--   Let $w$ be nonnegative rational edge weights on $n$ vertices and let $L$ be feasible for the level-$n$ Pauli moment relaxation on $n$ qubits, so that the real Gram matrix is indexed by all $4^n$ Pauli words. Then
--
--   $$\sum_{i<j}w_{ij}\,\frac{1-L(X_iX_j)-L(Y_iY_j)-L(Z_iZ_j)}{2}\le\lambda_{\max}(H_G),\qquad H_G=\sum_{i<j}w_{ij}(I-\mathrm{SWAP}_{ij}).$$
--
--   Together with the state embedding this says the level-$n$ value equals the optimum.
-- source:
--   Gribling, Sinjorgo and Sotirov, arXiv:2504.11120v1, Lemma 2.1 (exactness of SDP^n). The proof here is direct: a Hermitian square root of $\lambda_{\max}I-H_G$ expanded in the Pauli basis, instead of the flat extension theorem.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.PauliSDP.full_level_exact {n : ℕ}
    (w : QuantumMaxCutEnergy.Weights n)
    (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ)
    (hL : QuantumMaxCutEnergy.PauliSDP.Feasible n L) :
    QuantumMaxCutEnergy.PauliSDP.objective w L ≤ QuantumMaxCutEnergy.optimum ⟨n, w⟩ := by sorry

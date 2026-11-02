-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_exists_unit_correlation
-- name    : QuantumMaxCutEnergy.PauliSDP.exists_unit_correlation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T04:30:47.774411+00:00
-- url     : https://prove2.me/theorems/2108aa66-828b-43fb-8321-d6607f3a7a41
-- title:
--   Moment → Gram bridge: unit vectors realising the level-2 edge correlations
-- statement:
--   The Gram/vector bridge from level-2 Pauli moments to an explicit vector solution.
--
--   For every feasible level-$k$ ($k\ge 2$) moment solution $L$ there exist unit vectors $u_i$ in $\mathbb{R}^3 \otimes \mathbb{R}^{|\mathrm{Index}|}$ — a Bloch block times the moment-matrix index block — such that for every edge $e = \{i,j\}$
--   $$\langle u_i, u_j\rangle = \frac{L(X_iX_j) + L(Y_iY_j) + L(Z_iZ_j)}{3}.$$
--   Thus the edge expectation coefficient $c_e = (1+3s_e)/2$ is $1/2 - \tfrac32\langle u_i,u_j\rangle$-shaped in the vector solution, exactly the interface that hyperplane/GP rounding and the matching-state analysis consume. The proof factorises the positive semidefinite moment matrix as a Gram matrix (without matrix square roots) and normalises the three Pauli blocks at each vertex. **Formalization Note.** The target space is `EuclideanSpace ℝ (Fin 3 × Index n k)`; orthonormality of the three Pauli block vectors at each vertex is among the file's lemmas.
-- source:
--   Extracted from the level-2 Quantum Max-Cut analysis of Eunou Lee and Ojas Parekh, ICALP 2024, https://arxiv.org/abs/2401.03616

import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators
open QuantumMaxCutEnergy.PauliSDP

theorem QuantumMaxCutEnergy.PauliSDP.exists_unit_correlation {n k : ℕ} (hk : 2 ≤ k) (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ) (hL : QuantumMaxCutEnergy.PauliSDP.Feasible k L) :
    ∃ u : Fin n → EuclideanSpace ℝ (Fin 3 × QuantumMaxCutEnergy.PauliSDP.Index n k),
      (∀ i, ‖u i‖ = 1) ∧
      ∀ e : QuantumMaxCutEnergy.Edge n, inner ℝ (u e.val.1) (u e.val.2) =
        (L (QuantumMaxCutEnergy.PauliSDP.twoBody 1 e) + L (QuantumMaxCutEnergy.PauliSDP.twoBody 2 e) + L (QuantumMaxCutEnergy.PauliSDP.twoBody 3 e)) / 3 := by sorry

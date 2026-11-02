-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_exists_lee_vector
-- name    : QuantumMaxCutEnergy.PauliSDP.exists_lee_vector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T15:35:00.982215+00:00
-- url     : https://prove2.me/theorems/6042236c-4724-4cde-b712-10f2164ea415
-- title:
--   Concrete Pauli moments satisfy Lee’s vector relaxation
-- statement:
--   For every level $k\ge2$, each feasible canonical Pauli moment assignment admits finite-dimensional real Gram vectors satisfying all of the explicit constraints in Lee’s vector relaxation. Its edge-vector correlation with the identity vector is exactly the sum of the three corresponding Pauli moments. No star or triangle inequality is assumed in constructing these vectors.
-- source:
--   Lee, Optimizing quantum circuit parameters via SDP, ISAAC 2022; public arXiv:2209.00789v1, Definition 5 and Lemma 2. This result explicitly maps the campaign’s canonical phase-aware Pauli moment matrix to the vector constraints. https://arxiv.org/abs/2209.00789

import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Definitions.Def_QMaxCutSDP_Rounding_Model
import Mathlib
open scoped BigOperators
open Matrix

theorem QuantumMaxCutEnergy.PauliSDP.exists_lee_vector {n k : ℕ} (hk : 2 ≤ k)
    (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ)
    (hL : QuantumMaxCutEnergy.PauliSDP.Feasible k L) :
    ∃ v : QMaxCutSDP.Rounding.SDPVec n
        (Fintype.card (QuantumMaxCutEnergy.PauliSDP.Index n k)),
      QMaxCutSDP.Rounding.IsSFeasible v ∧
      ∀ i j : Fin n, QMaxCutSDP.Rounding.vEdge v i j ⬝ᵥ v.v0 =
        L (fun t => if t = i ∨ t = j then 1 else 0) +
        L (fun t => if t = i ∨ t = j then 2 else 0) +
        L (fun t => if t = i ∨ t = j then 3 else 0) := by sorry

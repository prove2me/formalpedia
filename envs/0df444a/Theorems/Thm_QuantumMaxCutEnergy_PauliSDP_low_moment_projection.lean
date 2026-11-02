-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_low_moment_projection
-- name    : QuantumMaxCutEnergy.PauliSDP.low_moment_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T15:11:20.801981+00:00
-- url     : https://prove2.me/theorems/6692d8e1-f343-43b7-ac8d-59fde3130724
-- title:
--   Pauli feasibility and energy use only moments of support at most twice the level
-- statement:
--   Fix $k\ge2$. If two real moment assignments agree on every canonical Pauli word of support at most $2k$, then either both satisfy the level-$k$ Pauli moment constraints or neither does, and they have the same energy objective for every nonnegative weighted graph. This removes the inactive moment coordinates from the numerical relaxation without changing feasibility or its objective. A polynomial-size encoding and an optimization algorithm require additional proofs.
-- source:
--   Gribling, Sinjorgo and Sotirov, public arXiv2504.11120v1, Section2, canonical Pauli moment SDP and its active word index set, https://arxiv.org/html/2504.11120v1#S2 . Elementary feasibility, degree, and objective bounds for the explicit formal relaxation; these are supporting well-posedness/projection results, not a completed solver theorem.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.PauliSDP.low_moment_projection
    {n k : ℕ} (hk : 2 ≤ k)
    (L L' : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ)
    (h : ∀ P : QuantumMaxCutEnergy.PauliSDP.Word n,
      (QuantumMaxCutEnergy.PauliSDP.support P).card ≤ 2 * k → L P = L' P) :
    (QuantumMaxCutEnergy.PauliSDP.Feasible k L ↔
      QuantumMaxCutEnergy.PauliSDP.Feasible k L') ∧
    ∀ w : QuantumMaxCutEnergy.Weights n,
      QuantumMaxCutEnergy.PauliSDP.objective w L =
        QuantumMaxCutEnergy.PauliSDP.objective w L' := by sorry

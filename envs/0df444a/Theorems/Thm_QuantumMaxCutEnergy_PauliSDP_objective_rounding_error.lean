-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_objective_rounding_error
-- name    : QuantumMaxCutEnergy.PauliSDP.objective_rounding_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T15:48:12.019421+00:00
-- url     : https://prove2.me/theorems/ac82244b-0244-4b3d-911d-89554d5cb9e7
-- title:
--   Certified objective error under moment rounding
-- statement:
--   Let $L,L'$ be real Pauli moment assignments on a graph with nonnegative weights and total weight $W$. If $|L(P)-L'(P)|\le\delta$ for every word of support at most two, then
--
--   $$|J(L)-J(L')|\le\frac32\delta W.$$
--
--   Here $J$ uses the campaign Hamiltonian normalization $H_G=\sum_{ij}w_{ij}(I-\mathrm{SWAP}_{ij})$.
-- source:
--   Gribling, Sinjorgo and Sotirov, arXiv:2504.11120v1, Section 2, Eqs. (2.3)–(2.4): https://arxiv.org/html/2504.11120v1#S2 . The quantitative conditioning and perturbation estimates are elementary consequences of the explicitly defined Pauli moment matrix.

import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators
open Matrix

theorem QuantumMaxCutEnergy.PauliSDP.objective_rounding_error {n : ℕ}
    (w : QuantumMaxCutEnergy.Weights n)
    (L L' : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ) (δ : ℝ)
    (hclose : ∀ P : QuantumMaxCutEnergy.PauliSDP.Word n,
      (QuantumMaxCutEnergy.PauliSDP.support P).card ≤ 2 → |L P - L' P| ≤ δ) :
    |QuantumMaxCutEnergy.PauliSDP.objective w L - QuantumMaxCutEnergy.PauliSDP.objective w L'| ≤
      (3 * δ / 2) * (∑ e, (w e : ℝ)) := by sorry

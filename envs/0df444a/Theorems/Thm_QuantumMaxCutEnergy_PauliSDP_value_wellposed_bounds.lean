-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_value_wellposed_bounds
-- name    : QuantumMaxCutEnergy.PauliSDP.value_wellposed_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T15:11:19.458953+00:00
-- url     : https://prove2.me/theorems/f290f34b-acf0-40a0-aca2-1d4485df7d94
-- title:
--   The Pauli relaxation value is well defined and bounded
-- statement:
--   For every fixed level $k\ge2$ and every graph $G$ with nonnegative rational weights, the specified Pauli moment SDP has a feasible moment assignment and its value satisfies
--
--   $$\tfrac12 W(G)\le U_k(G)\le2W(G).$$
--
--   If all weights are zero, then $U_k(G)=0$. This includes empty graphs. The result establishes nondegeneracy and finite objective bounds for the concrete relaxation; its relation to the quantum optimum and a polynomial-time solver remain separate obligations.
-- source:
--   Gribling, Sinjorgo and Sotirov, public arXiv2504.11120v1, Section2, canonical Pauli moment SDP and its active word index set, https://arxiv.org/html/2504.11120v1#S2 . Elementary feasibility, degree, and objective bounds for the explicit formal relaxation; these are supporting well-posedness/projection results, not a completed solver theorem.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.PauliSDP.value_wellposed_bounds
    (k : ℕ) (hk : 2 ≤ k) (G : QuantumMaxCutEnergy.Input) :
    (∃ L : QuantumMaxCutEnergy.PauliSDP.Word G.n → ℝ,
      QuantumMaxCutEnergy.PauliSDP.Feasible k L) ∧
    (∑ e, (G.weights e : ℝ)) / 2 ≤ QuantumMaxCutEnergy.PauliSDP.value k G ∧
    QuantumMaxCutEnergy.PauliSDP.value k G ≤ 2 * ∑ e, (G.weights e : ℝ) ∧
    ((∀ e, G.weights e = 0) → QuantumMaxCutEnergy.PauliSDP.value k G = 0) := by sorry

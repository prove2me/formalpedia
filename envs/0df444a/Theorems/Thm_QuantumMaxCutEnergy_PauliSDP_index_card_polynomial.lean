-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_index_card_polynomial
-- name    : QuantumMaxCutEnergy.PauliSDP.index_card_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T15:45:33.695242+00:00
-- url     : https://prove2.me/theorems/f98ae282-75ba-49cf-9e62-bae2942be622
-- title:
--   Polynomial cardinality of Pauli Gram and moment indices
-- statement:
--   For every number $n$ of vertices and every level $k$, the actual canonical Pauli word index set of support at most $k$ has cardinality at most $(3n+1)^k$. The support-at-most-$2k$ active moment index has cardinality at most $(3n+1)^{2k}$. Hence both dimensions are polynomial in $n$ when the level is fixed, including empty instances and level zero.
-- source:
--   Elementary counting for the explicit canonical Pauli word hierarchy; compare Gribling, Sinjorgo and Sotirov, public arXiv:2504.11120v1, Section 2. This is a verified dimension bound, not a complete SDP-solver theorem. https://arxiv.org/html/2504.11120v1#S2

import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib

theorem QuantumMaxCutEnergy.PauliSDP.index_card_polynomial (n k : ℕ) :
    Fintype.card (QuantumMaxCutEnergy.PauliSDP.Index n k) ≤ (3 * n + 1) ^ k ∧
    Fintype.card (QuantumMaxCutEnergy.PauliSDP.Index n (2 * k)) ≤ (3 * n + 1) ^ (2 * k) := by sorry

-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_moment_star_bound
-- name    : QuantumMaxCutEnergy.PauliSDP.moment_star_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T15:53:31.094932+00:00
-- url     : https://prove2.me/theorems/c0b5f99c-b784-498d-86c7-a5170ee6f12c
-- title:
--   Star monogamy for the concrete Pauli moment relaxation
-- statement:
--   For every feasible level-$k$ Pauli moment assignment with $k\ge2$, every vertex $i$, and every set $T$ of other vertices,
--
--   $$\sum_{j\in T} e_{ij}(L)\le |T|+1,$$
--
--   where $e_{ij}(L)=(1-L(X_iX_j)-L(Y_iY_j)-L(Z_iZ_j))/2$ is the campaign-normalized edge energy.
-- source:
--   Lee, Optimizing quantum circuit parameters via SDP, ISAAC 2022; public arXiv:2209.00789v1, Lemma 4, Eq. (13), combined with the proved canonical Pauli-to-vector representation. The factor of two converts Lee’s singlet-projector normalization to the campaign’s I-SWAP normalization. https://arxiv.org/abs/2209.00789

import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators
open QuantumMaxCutEnergy.PauliSDP

theorem QuantumMaxCutEnergy.PauliSDP.moment_star_bound {n k : ℕ} (hk : 2 ≤ k)
    (L : Word n → ℝ) (hL : Feasible k L) (i : Fin n)
    (T : Finset (Fin n)) (hi : i ∉ T) :
    (∑ j ∈ T, (1 - L (fun t => if t = i ∨ t = j then 1 else 0) -
      L (fun t => if t = i ∨ t = j then 2 else 0) -
      L (fun t => if t = i ∨ t = j then 3 else 0)) / 2) ≤
      (T.card : ℝ) + 1 := by sorry

-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_moment_triangle_bound
-- name    : QuantumMaxCutEnergy.PauliSDP.moment_triangle_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T16:01:58.259961+00:00
-- url     : https://prove2.me/theorems/af2d3b19-9c32-403f-9d2b-c066dde5cc6b
-- title:
--   Triangle energy bound for the concrete Pauli relaxation
-- statement:
--   For every feasible level-$k$ Pauli moment assignment with $k\ge2$ and every three distinct vertices $i,j,\ell$,
--
--   $$e_{ij}(L)+e_{i\ell}(L)+e_{j\ell}(L)\le3,$$
--
--   where $e_{ab}(L)=(1-L(X_aX_b)-L(Y_aY_b)-L(Z_aZ_b))/2$.
-- source:
--   A direct consequence of the signed Pauli multiplication identities in Lee’s vector relaxation, Definition 5 and Lemma 3 of Lee, ISAAC 2022, public arXiv:2209.00789v1. https://arxiv.org/abs/2209.00789

import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators
open QuantumMaxCutEnergy.PauliSDP

theorem QuantumMaxCutEnergy.PauliSDP.moment_triangle_bound {n k : ℕ} (hk : 2 ≤ k)
    (L : Word n → ℝ) (hL : Feasible k L)
    (i j l : Fin n) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    (1 - L (fun t => if t = i ∨ t = j then 1 else 0) -
      L (fun t => if t = i ∨ t = j then 2 else 0) -
      L (fun t => if t = i ∨ t = j then 3 else 0)) / 2 +
    (1 - L (fun t => if t = i ∨ t = l then 1 else 0) -
      L (fun t => if t = i ∨ t = l then 2 else 0) -
      L (fun t => if t = i ∨ t = l then 3 else 0)) / 2 +
    (1 - L (fun t => if t = j ∨ t = l then 1 else 0) -
      L (fun t => if t = j ∨ t = l then 2 else 0) -
      L (fun t => if t = j ∨ t = l then 3 else 0)) / 2 ≤ 3 := by sorry

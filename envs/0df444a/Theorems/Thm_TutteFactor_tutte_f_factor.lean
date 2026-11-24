-- Prove2me | Theorems.Thm_TutteFactor_tutte_f_factor
-- name    : TutteFactor.tutte_f_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:19:08.125067+00:00
-- url     : https://prove2.me/theorems/1517779c-a21e-4f1c-b621-61960933ce4b
-- title:
--   Tutte Factor: tutte f factor
-- statement:
--   **Tutte's f-factor theorem.** A finite simple graph `G` has a spanning subgraph `H` with
--   `deg_H v = f v` for every vertex `v` if and only if, for all disjoint vertex sets `S` and `T`,
--   `q(S, T) ≤ ∑_{v ∈ S} f v − ∑_{v ∈ T} f v + ∑_{v ∈ T} deg_{G − S} v`.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/Solution.lean#L44-L49
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/Solution.lean#L44-L49

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactor
public import Definitions.Def_FFactorLib_Solution
public import Theorems.Thm_FFactor_tutte_f_factor

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open TutteFactor
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem TutteFactor.tutte_f_factor (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℕ) :
    (∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, H ≤ G ∧ ∀ v, H.degree v = f v) ↔
      ∀ S T : Finset V, Disjoint S T →
        (oddCount G f S T : ℤ) ≤ ∑ v ∈ S, (f v : ℤ) - ∑ v ∈ T, (f v : ℤ) +
          ∑ v ∈ T, (#{u ∈ G.neighborFinset v | u ∉ S} : ℤ) := by sorry

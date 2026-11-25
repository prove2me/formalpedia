-- Prove2me | Theorems.Thm_SimpleGraph_exists_perm_subset
-- name    : SimpleGraph.exists_perm_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:43:21.264928+00:00
-- url     : https://prove2.me/theorems/ca7ddb17-0fc6-4e8e-a0ec-bdea6efaee58
-- title:
--   Simple Graph: exists perm subset
-- statement:
--   **Hall para digrafos regulares.** Si cada vértice tiene `k ≥ 1` arcos salientes y `k`
--   entrantes en `D`, existe una permutación `σ` con `(v, σ v) ∈ D` para todo `v`.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Petersen.lean#L42-L84
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Petersen.lean#L42-L84

module
public import Definitions.Def_Euler_Orientation
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Set.Card
public import Definitions.Def_Euler_Petersen
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem SimpleGraph.exists_perm_subset {D : Finset (V × V)} {k : ℕ} (hk : 0 < k)
    (hout : ∀ v, (D.filter fun p => p.1 = v).card = k)
    (hin : ∀ v, (D.filter fun p => p.2 = v).card = k) :
    ∃ σ : Equiv.Perm V, ∀ v, (v, σ v) ∈ D := by sorry

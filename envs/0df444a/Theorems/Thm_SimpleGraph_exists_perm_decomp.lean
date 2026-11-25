-- Prove2me | Theorems.Thm_SimpleGraph_exists_perm_decomp
-- name    : SimpleGraph.exists_perm_decomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:43:27.723904+00:00
-- url     : https://prove2.me/theorems/a0074c80-187c-49ec-b343-68570bd6f0db
-- title:
--   Simple Graph: exists perm decomp
-- statement:
--   **Descomposición en permutaciones.** Un digrafo `k`-regular (de entrada y salida) se parte
--   en `k` permutaciones con arcos disjuntos.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Petersen.lean#L88-L163
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Petersen.lean#L88-L163

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

theorem SimpleGraph.exists_perm_decomp : ∀ (k : ℕ) (D : Finset (V × V)),
    (∀ v, (D.filter fun p => p.1 = v).card = k) → (∀ v, (D.filter fun p => p.2 = v).card = k) →
    ∃ σ : Fin k → Equiv.Perm V, (∀ i v, (v, σ i v) ∈ D) ∧
      (∀ i j v, σ i v = σ j v → i = j) ∧ (∀ p ∈ D, ∃ i, σ i p.1 = p.2) := by sorry

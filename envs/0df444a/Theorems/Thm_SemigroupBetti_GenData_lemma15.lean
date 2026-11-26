-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_lemma15
-- name    : SemigroupBetti.GenData.lemma15
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:06:15.609356+00:00
-- url     : https://prove2.me/theorems/3d1d9c5b-f75f-4806-ac0f-d8f854e2ebfd
-- title:
--   Gen Data: lemma15
-- statement:
--   **Lemma 15.** If `A = 1`, `B = W - 1` and `Q = W - 2`, then some `𝓠` degree has selected
--   `13`-vector with `u = 1`, and every such vector is exactly `(0,1,0,W-2)`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L232-L269
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L232-L269

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.lemma15 (hA : G.A = 1) (hB : G.B = G.W - 1) (hQ : G.Q = G.W - 2) :
    (∃ D ∈ G.famQ, G.sel D {1, 3} 1 = 1) ∧
      ∀ D ∈ G.famQ, G.sel D {1, 3} 1 = 1 → G.sel D {1, 3} = ![0, 1, 0, G.W - 2] := by sorry

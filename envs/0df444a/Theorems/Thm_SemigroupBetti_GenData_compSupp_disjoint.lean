-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_compSupp_disjoint
-- name    : SemigroupBetti.GenData.compSupp_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:24.992687+00:00
-- url     : https://prove2.me/theorems/7830c6ef-1a54-5a6a-a5da-88535b524854
-- title:
--   Gen Data: comp Supp disjoint
-- statement:
--   **Lemma 2.1.** Distinct components of `∇_d` have disjoint supports.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L141-L147
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L141-L147

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.compSupp_disjoint {d : ℕ} {C C' : (G.nabla d).ConnectedComponent} (h : C ≠ C') :
    Disjoint (G.compSupp C) (G.compSupp C') := by sorry

-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_exists_supp_eq
-- name    : SemigroupBetti.GenData.exists_supp_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:01:59.806032+00:00
-- url     : https://prove2.me/theorems/b36845eb-138c-48f4-a1b3-e36d6f5facd5
-- title:
--   Gen Data: exists supp eq
-- statement:
--   A component with support `K` of size two contains a factorization with support exactly `K`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L102-L110
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L102-L110

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.exists_supp_eq {d : ℕ} {C : (G.nabla d).ConnectedComponent} {K : Finset (Fin 4)}
    (hK : K.card = 2) (hC : G.compSupp C = K) :
    ∃ z : G.fiber d, (G.nabla d).connectedComponentMk z = C ∧ supp z.1 = K := by sorry

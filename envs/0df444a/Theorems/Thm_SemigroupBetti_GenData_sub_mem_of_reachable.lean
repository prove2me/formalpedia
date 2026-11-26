-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_sub_mem_of_reachable
-- name    : SemigroupBetti.GenData.sub_mem_of_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:01:29.468632+00:00
-- url     : https://prove2.me/theorems/2bec8ef8-9e81-4b7e-929f-48d243a4cb82
-- title:
--   Gen Data: sub mem of reachable
-- statement:
--   Path step (write-up Lemma 0D).
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L170-L178
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L170-L178

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]

theorem SemigroupBetti.GenData.sub_mem_of_reachable {J : Ideal (MvPolynomial (Fin 4) K)} {d : ℕ}
    (IH : ∀ e < d, ∀ z z' : Fin 4 → ℕ, G.nu z = e → G.nu z' = e → mono K z - mono K z' ∈ J)
    {x y : G.fiber d} (h : (G.nabla d).Reachable x y) : mono K x.1 - mono K y.1 ∈ J := by sorry

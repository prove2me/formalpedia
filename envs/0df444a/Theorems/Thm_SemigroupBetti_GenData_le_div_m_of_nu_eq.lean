-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_le_div_m_of_nu_eq
-- name    : SemigroupBetti.GenData.le_div_m_of_nu_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:30:29.468136+00:00
-- url     : https://prove2.me/theorems/35e5c9e9-405d-599e-98f1-a93b7d9b17d4
-- title:
--   Gen Data: le div m of nu eq
-- statement:
--   Every factorization of `d` lies in the box `{0,…,d/m}⁴` (Lemma 0A, first paragraph).
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L33-L35
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L33-L35

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

theorem SemigroupBetti.GenData.le_div_m_of_nu_eq {z : Fin 4 → ℕ} {d : ℕ} (h : G.nu z = d) (i : Fin 4) :
    z i ≤ d / G.m := by sorry

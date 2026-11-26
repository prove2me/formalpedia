-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_compSupp_nonempty
-- name    : SemigroupBetti.GenData.compSupp_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:23.330879+00:00
-- url     : https://prove2.me/theorems/53df6879-2501-419c-b7c5-93e15f5bee1c
-- title:
--   Gen Data: comp Supp nonempty
-- statement:
--   **Lemma 2.2.** At positive degree every component has nonempty support.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L150-L158
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L150-L158

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

theorem SemigroupBetti.GenData.compSupp_nonempty {d : ℕ} (hd : 0 < d) (C : (G.nabla d).ConnectedComponent) :
    (G.compSupp C).Nonempty := by sorry

-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_beta1_eq_sum_of_le
-- name    : SemigroupBetti.GenData.beta1_eq_sum_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:53.441158+00:00
-- url     : https://prove2.me/theorems/990a563c-b9ca-446e-a10e-6853e5b06be2
-- title:
--   Gen Data: beta1 eq sum of le
-- statement:
--   The bounded definition of `β₁` agrees with any larger cutoff.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L236-L243
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean#L236-L243

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

theorem SemigroupBetti.GenData.beta1_eq_sum_of_le {K : ℕ} (hK : G.H ≤ K) :
    G.beta1 = ∑ d ∈ range (K + 1), (G.ncomp d - 1) := by sorry

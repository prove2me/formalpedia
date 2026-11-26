-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_general_bound_eq
-- name    : SemigroupBetti.GenData.general_bound_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:04:40.999607+00:00
-- url     : https://prove2.me/theorems/4d37dd05-bb0a-40fd-a98b-f72ca6c089af
-- title:
--   Gen Data: general bound eq
-- statement:
--   **Lemma 13 (closed form).** `4 + 2(R-1) + (p+q-1) = 2W - 2 max(s,t) + (s+t)/d + 1`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Arith.lean#L34-L39
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Arith.lean#L34-L39

module
public import Definitions.Def_SemigroupBetti_Antichain
public import Definitions.Def_SemigroupBetti_Arith
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.general_bound_eq :
    4 + 2 * (G.R - 1) + (G.p + G.q - 1) = 2 * G.W - 2 * max G.s G.t + (G.s + G.t) / G.dg + 1 := by sorry

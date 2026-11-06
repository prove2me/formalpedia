-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGreedyScan_join
-- name    : QEC.Locality.daiLiGreedyScan_join
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:05:48.258539+00:00
-- url     : https://prove2.me/theorems/c1244337-d790-4578-b91b-8520de4e563c
-- title:
--   Locality: dai Li Greedy Scan join
-- statement:
--   The greedy scan preserves the finite half-open atom order exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L669-L691
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L669-L691

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

theorem QEC.Locality.daiLiGreedyScan_join (d : Nat) :
    ∀ (remaining pending : List DaiLiAtomicCounter)
      (emitted : List (List DaiLiAtomicCounter)),
      (daiLiGreedyScan d remaining pending emitted).flatten =
        emitted.reverse.flatten ++ pending ++ remaining := by sorry

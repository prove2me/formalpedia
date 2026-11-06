-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGreedyScanWith_join
-- name    : QEC.Locality.daiLiGreedyScanWith_join
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:01.759931+00:00
-- url     : https://prove2.me/theorems/6f0518e0-acf6-4455-90a5-c1d0e0490fad
-- title:
--   Locality: dai Li Greedy Scan With join
-- statement:
--   The payload scan preserves the finite atom order exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L942-L965
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L942-L965

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

theorem QEC.Locality.daiLiGreedyScanWith_join {α : Type*} (weight : α → Nat) (d : Nat) :
    ∀ (remaining pending : List α) (emitted : List (List α)),
      (daiLiGreedyScanWith weight d remaining pending emitted).flatten =
        emitted.reverse.flatten ++ pending ++ remaining := by sorry

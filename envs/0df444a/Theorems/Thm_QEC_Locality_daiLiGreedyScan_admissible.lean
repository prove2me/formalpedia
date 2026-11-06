-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGreedyScan_admissible
-- name    : QEC.Locality.daiLiGreedyScan_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:05:44.731878+00:00
-- url     : https://prove2.me/theorems/b8563e85-c4ca-447c-9dad-f9d037d64b4f
-- title:
--   Locality: dai Li Greedy Scan admissible
-- statement:
--   The emitted family has no empty pieces and every piece is low-counter or short.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L694-L753
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L694-L753

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

theorem QEC.Locality.daiLiGreedyScan_admissible (d : Nat) :
    ∀ (remaining pending : List DaiLiAtomicCounter)
      (emitted : List (List DaiLiAtomicCounter)),
      (pending = [] ∨ DaiLiLowCounter d pending) →
      (∀ piece ∈ emitted, DaiLiAtomicPieceAdmissible d piece) →
      ∀ piece ∈ daiLiGreedyScan d remaining pending emitted,
        DaiLiAtomicPieceAdmissible d piece := by sorry

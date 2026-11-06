-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGreedyScan_count
-- name    : QEC.Locality.daiLiGreedyScan_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:05:56.942713+00:00
-- url     : https://prove2.me/theorems/80cab8ea-3fe9-4525-a0c7-ffe81c39c7b2
-- title:
--   Locality: dai Li Greedy Scan count
-- statement:
--   Every threshold crossing emits at most two pieces and pays for them with the
--   counter in the just-completed prefix.  A final pending low piece accounts for
--   the one additive `d` in the corrected bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L760-L811
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L760-L811

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

theorem QEC.Locality.daiLiGreedyScan_count (d : Nat) :
    ∀ (remaining pending : List DaiLiAtomicCounter)
      (emitted : List (List DaiLiAtomicCounter)),
      emitted.length * d ≤ 20 * daiLiAtomicPiecesMass emitted →
      (daiLiGreedyScan d remaining pending emitted).length * d ≤
        20 * (daiLiAtomicPiecesMass emitted + daiLiAtomicMass pending +
          daiLiAtomicMass remaining) + d := by sorry

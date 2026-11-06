-- Prove2me | Theorems.Thm_QEC_Locality_daiLiRectangleQubitsCover_groups
-- name    : QEC.Locality.daiLiRectangleQubitsCover_groups
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:07:08.400971+00:00
-- url     : https://prove2.me/theorems/e9c7f4ae-1b9e-4aa0-b186-baa5f5f0ec18
-- title:
--   Locality: dai Li Rectangle Qubits Cover groups
-- statement:
--   Replacing atom groups by their equal collapsed rectangle covers commutes with folding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1367-L1399
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1367-L1399

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

theorem QEC.Locality.daiLiRectangleQubitsCover_groups
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (groups : List (List (ℝ × ℝ)))
    (hGroups : ∀ group ∈ groups,
      embedding.qubitsInRectangle (daiLiAtomGroupRectangle left right group).1
          (daiLiAtomGroupRectangle left right group).2 =
        daiLiAtomQubitsCover embedding left right group) :
    daiLiRectangleQubitsCover embedding
        (groups.map (daiLiAtomGroupRectangle left right)) =
      daiLiAtomQubitsCover embedding left right groups.flatten := by sorry

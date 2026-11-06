-- Prove2me | Theorems.Thm_QEC_Locality_daiLiAtomGroupsCover_pairwise
-- name    : QEC.Locality.daiLiAtomGroupsCover_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:07:01.02796+00:00
-- url     : https://prove2.me/theorems/0e033131-7a2c-4daa-a1d3-fd4734ada4c9
-- title:
--   Locality: dai Li Atom Groups Cover pairwise
-- statement:
--   Pairwise atom disjointness lifts to the finite covers of contiguous atom groups.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1456-L1484
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1456-L1484

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

theorem QEC.Locality.daiLiAtomGroupsCover_pairwise
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (groups : List (List (ℝ × ℝ)))
    (hPairwise : (groups.flatten.map (daiLiAtomQubits embedding left right)).Pairwise Disjoint) :
    (groups.map (daiLiAtomQubitsCover embedding left right)).Pairwise Disjoint := by sorry

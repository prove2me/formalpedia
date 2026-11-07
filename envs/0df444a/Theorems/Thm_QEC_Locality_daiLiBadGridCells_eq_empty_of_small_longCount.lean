-- Prove2me | Theorems.Thm_QEC_Locality_daiLiBadGridCells_eq_empty_of_small_longCount
-- name    : QEC.Locality.daiLiBadGridCells_eq_empty_of_small_longCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:14:28.495909+00:00
-- url     : https://prove2.me/theorems/165f8d33-5611-4c26-a3c1-8d5feb087426
-- title:
--   Locality: dai Li Bad Grid Cells eq empty of small long Count
-- statement:
--   Case 2 has no bad grid cells once the actual total long-incidence count is
--   below `d / 10`.  This turns the paper's "fewer than one bad rectangle" step
--   into a finite contradiction, rather than accepting an empty rectangle list.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L631-L653
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L631-L653

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableDGeK

theorem QEC.Locality.daiLiBadGridCells_eq_empty_of_small_longCount
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w : ℝ) (d : ℕ)
    (origin : ℝ × ℝ)
    (hGlobal : 10 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) < d) :
    daiLiBadGridCells P embedding threshold d w origin = ∅ := by sorry

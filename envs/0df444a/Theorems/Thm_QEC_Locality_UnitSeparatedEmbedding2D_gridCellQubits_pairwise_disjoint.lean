-- Prove2me | Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_gridCellQubits_pairwise_disjoint
-- name    : QEC.Locality.UnitSeparatedEmbedding2D.gridCellQubits_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:36:29.052096+00:00
-- url     : https://prove2.me/theorems/ad5144e6-63d1-48ad-b489-a87e07e84943
-- title:
--   Unit Separated Embedding2 D: grid Cell Qubits pairwise disjoint
-- statement:
--   Different occupied cell indices select disjoint finite qubit regions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L134-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean#L134-L146

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable

theorem QEC.Locality.UnitSeparatedEmbedding2D.gridCellQubits_pairwise_disjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ) (origin : ℝ × ℝ) :
    (↑(embedding.gridOccupiedCells w origin) : Set (ℤ × ℤ)).PairwiseDisjoint
      (embedding.gridCellQubits w origin) := by sorry

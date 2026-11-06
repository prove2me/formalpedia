-- Prove2me | Theorems.Thm_QEC_Locality_fixedGeneratorOuterBoundary_square_subset_growthBoundary
-- name    : QEC.Locality.fixedGeneratorOuterBoundary_square_subset_growthBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:03:18.369275+00:00
-- url     : https://prove2.me/theorems/e1224a66-0104-4f66-bcb8-7d0cbd640187
-- title:
--   Locality: fixed Generator Outer Boundary square subset growth Boundary
-- statement:
--   Every actual fixed-generator outer-boundary qubit of the inner square is in the
--   computed growth boundary: shell qubits are included geometrically, and qubits
--   beyond the shell are included only after proving their interaction is long.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L377-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L377-L400

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive

theorem QEC.Locality.fixedGeneratorOuterBoundary_square_subset_growthBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerRadius threshold : ℝ) :
    P.fixedGeneratorOuterBoundary
        ((squareSubsystem embedding center (outerRadius - threshold)).selected : Set ι) ⊆
      ((squareGrowthBoundary P embedding center outerRadius threshold).selected : Set ι) := by sorry

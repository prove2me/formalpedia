-- Prove2me | Theorems.Thm_QEC_Locality_BGKLSeparatorSplit_right_rpow_le
-- name    : QEC.Locality.BGKLSeparatorSplit.right_rpow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:31.629686+00:00
-- url     : https://prove2.me/theorems/378f99a2-d768-4ea9-862a-554b3b91b32a
-- title:
--   BGKLSeparator Split: right rpow le
-- statement:
--   `2/3` balance gives the corresponding real-power decay for the right child.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L350-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L350-L362

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.BGKLSeparatorSplit.right_rpow_le
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices)
    {exponent : ℝ} (hexponent : 0 ≤ exponent) :
    Real.rpow split.right.card exponent ≤
      bgklDecayRatio exponent * Real.rpow vertices.card exponent := by sorry

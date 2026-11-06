-- Prove2me | Theorems.Thm_QEC_Locality_BGKLSeparatorSplit_left_rpow_le
-- name    : QEC.Locality.BGKLSeparatorSplit.left_rpow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:32.897137+00:00
-- url     : https://prove2.me/theorems/da72f1c7-e756-4bec-891b-811497564f0a
-- title:
--   BGKLSeparator Split: left rpow le
-- statement:
--   `2/3` balance gives the corresponding real-power decay for the left child.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L335-L347
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L335-L347

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

theorem QEC.Locality.BGKLSeparatorSplit.left_rpow_le
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices)
    {exponent : ℝ} (hexponent : 0 ≤ exponent) :
    Real.rpow split.left.card exponent ≤
      bgklDecayRatio exponent * Real.rpow vertices.card exponent := by sorry

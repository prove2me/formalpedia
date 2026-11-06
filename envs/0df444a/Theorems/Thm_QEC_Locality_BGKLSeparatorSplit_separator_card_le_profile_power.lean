-- Prove2me | Theorems.Thm_QEC_Locality_BGKLSeparatorSplit_separator_card_le_profile_power
-- name    : QEC.Locality.BGKLSeparatorSplit.separator_card_le_profile_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:23.445198+00:00
-- url     : https://prove2.me/theorems/a066c578-35bd-4fe1-89ce-0d100ebd81c1
-- title:
--   BGKLSeparator Split: separator card le profile power
-- statement:
--   A selected minimum separator obeys the assumed measured profile bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L315-L332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L315-L332

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

theorem QEC.Locality.BGKLSeparatorSplit.separator_card_le_profile_power
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices)
    {beta exponent : ℝ}
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hvertices : 0 < vertices.card) :
    (split.separator.card : ℝ) ≤ beta * Real.rpow vertices.card exponent := by sorry

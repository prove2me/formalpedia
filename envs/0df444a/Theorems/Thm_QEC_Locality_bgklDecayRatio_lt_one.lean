-- Prove2me | Theorems.Thm_QEC_Locality_bgklDecayRatio_lt_one
-- name    : QEC.Locality.bgklDecayRatio_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:05:19.82221+00:00
-- url     : https://prove2.me/theorems/55b89785-9f52-4fb9-b2a8-80194f3bf520
-- title:
--   Locality: bgkl Decay Ratio lt one
-- statement:
--   The Locality construction uses the bgkl Decay Ratio lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L309-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L309-L312

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

theorem QEC.Locality.bgklDecayRatio_lt_one {exponent : ℝ} (hexponent : 0 < exponent) :
    bgklDecayRatio exponent < 1 := by sorry

-- Prove2me | Theorems.Thm_QEC_Locality_ancestorSeparatorUnion_card_le_sum
-- name    : QEC.Locality.ancestorSeparatorUnion_card_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:52.859992+00:00
-- url     : https://prove2.me/theorems/3c44d4db-d2b0-4450-9ba4-3e3c64405b24
-- title:
--   Locality: ancestor Separator Union card le sum
-- statement:
--   The union of a path's separators has at most the sum of their sizes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L479-L488
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L479-L488

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

theorem QEC.Locality.ancestorSeparatorUnion_card_le_sum
    {α : Type u} [DecidableEq α] (separators : List (Finset α)) :
    (ancestorSeparatorUnion separators).card ≤ ancestorSeparatorCardSum separators := by sorry

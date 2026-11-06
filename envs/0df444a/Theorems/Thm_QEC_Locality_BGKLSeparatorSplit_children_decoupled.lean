-- Prove2me | Theorems.Thm_QEC_Locality_BGKLSeparatorSplit_children_decoupled
-- name    : QEC.Locality.BGKLSeparatorSplit.children_decoupled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:48.92752+00:00
-- url     : https://prove2.me/theorems/9aedb5dd-0dc5-486f-beff-71cfb91c018d
-- title:
--   BGKLSeparator Split: children decoupled
-- statement:
--   The two child regions are fixed-generator decoupled, as required by #373.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L550-L559
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L550-L559

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

theorem QEC.Locality.BGKLSeparatorSplit.children_decoupled
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices) :
    P.fixedGeneratorDecoupled (split.left : Set ι) (split.right : Set ι) := by sorry

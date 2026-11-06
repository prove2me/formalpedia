-- Prove2me | Theorems.Thm_QEC_Locality_daiLiAtomGroupLower_eq_head
-- name    : QEC.Locality.daiLiAtomGroupLower_eq_head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:21.944759+00:00
-- url     : https://prove2.me/theorems/9400d118-8e8f-4da4-b998-40e6bca4ef54
-- title:
--   Locality: dai Li Atom Group Lower eq head
-- statement:
--   The Locality construction uses the dai Li Atom Group Lower eq head property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1087-L1092
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1087-L1092

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

theorem QEC.Locality.daiLiAtomGroupLower_eq_head
    (group : List (ℝ × ℝ)) (hGroup : group ≠ []) :
    daiLiAtomGroupLower group = (group.head hGroup).1 := by sorry

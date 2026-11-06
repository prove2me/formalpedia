-- Prove2me | Theorems.Thm_QEC_Locality_daiLiAtomGroupUpper_eq_getLast
-- name    : QEC.Locality.daiLiAtomGroupUpper_eq_getLast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:33.572195+00:00
-- url     : https://prove2.me/theorems/42b371f4-4105-480b-98ec-ce67437d00f3
-- title:
--   Locality: dai Li Atom Group Upper eq get Last
-- statement:
--   The Locality construction uses the dai Li Atom Group Upper eq get Last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1094-L1104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1094-L1104

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

theorem QEC.Locality.daiLiAtomGroupUpper_eq_getLast
    (group : List (ℝ × ℝ)) (hGroup : group ≠ []) :
    daiLiAtomGroupUpper group = (group.getLast hGroup).2 := by sorry

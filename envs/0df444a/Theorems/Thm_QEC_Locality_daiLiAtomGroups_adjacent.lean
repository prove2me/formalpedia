-- Prove2me | Theorems.Thm_QEC_Locality_daiLiAtomGroups_adjacent
-- name    : QEC.Locality.daiLiAtomGroups_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:25.78827+00:00
-- url     : https://prove2.me/theorems/48b592d3-b946-40a9-ac88-6900ae224ba7
-- title:
--   Locality: dai Li Atom Groups adjacent
-- statement:
--   The Locality construction uses the dai Li Atom Groups adjacent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1106-L1120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1106-L1120

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

theorem QEC.Locality.daiLiAtomGroups_adjacent
    (first second : List (ℝ × ℝ)) (hFirst : first ≠ []) (hSecond : second ≠ [])
    (hAdjacent : ∀ firstAtom ∈ first.getLast?, ∀ secondAtom ∈ second.head?,
      DaiLiAtomAdjacent firstAtom secondAtom) :
    daiLiAtomGroupUpper first = daiLiAtomGroupLower second := by sorry

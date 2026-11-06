-- Prove2me | Theorems.Thm_QEC_Locality_daiLiAtomGroup_short_height
-- name    : QEC.Locality.daiLiAtomGroup_short_height
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:34.804169+00:00
-- url     : https://prove2.me/theorems/5b2556c2-49c5-499c-8c83-8ef545528f6c
-- title:
--   Locality: dai Li Atom Group short height
-- statement:
--   A one-atom group inherits the exact Dai--Li short-height cap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1212-L1229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1212-L1229

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

theorem QEC.Locality.daiLiAtomGroup_short_height {ell : ℝ} :
    ∀ (group : List (ℝ × ℝ)), group ≠ [] → group.length ≤ 1 →
      (∀ atom ∈ group, DaiLiShortHeight ell atom.1 atom.2) →
        daiLiAtomGroupUpper group - daiLiAtomGroupLower group ≤ 10 * ell := by sorry

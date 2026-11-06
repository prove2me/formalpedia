-- Prove2me | Theorems.Thm_QEC_Locality_daiLiCorrectedFamilyCount_badRectangleVertexTerm_le
-- name    : QEC.Locality.daiLiCorrectedFamilyCount_badRectangleVertexTerm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:01:03.641924+00:00
-- url     : https://prove2.me/theorems/00bd7d6c-b8f4-483f-a581-1f5694098898
-- title:
--   Locality: dai Li Corrected Family Count bad Rectangle Vertex Term le
-- statement:
--   The Locality construction uses the dai Li Corrected Family Count bad Rectangle Vertex Term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1625-L1642
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1625-L1642

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

theorem QEC.Locality.daiLiCorrectedFamilyCount_badRectangleVertexTerm_le
    (M totalF d budget : Nat) (ell : ℝ) (hD : 0 < d)
    (hCount : M * d ≤ 30 * totalF) (hTotal : 50 * totalF ≤ budget) :
    384 * ell ^ 2 * (M : ℝ) ≤
      400 * ell ^ 2 * (budget : ℝ) / (d : ℝ) := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_inverse_residual_boundary
-- name    : QEC.Coding.BDL26RXErrorPullback.inverse_residual_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:56:26.370128+00:00
-- url     : https://prove2.me/theorems/2c619bfd-3237-4931-aa64-59a20d580209
-- title:
--   BDL26 RXError Pullback: inverse residual boundary
-- statement:
--   The proved quotient right inverse makes the entire forward discrepancy
--   an actual upper boundary, rather than just zero on a selected sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L118-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L118-L134

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RXCohomology BDL26AlternatingCochain
open BDL26RZCohomology (mem_cocycle_iff mem_boundary_iff)
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXErrorPullback.inverse_residual_boundary (h : i.val % 2 = 0)
    (w : Cocycle (state S (i.val + 1)).presentation) :
    (BDL26FiniteCohomology.stepCocycle S i.val (inverseCocycle S depth i h w) :
      Cocycle (state S (i.val + 1)).presentation) - w ∈
      (complex (state S (i.val + 1)).presentation).middleCoboundaryInCocycles := by sorry

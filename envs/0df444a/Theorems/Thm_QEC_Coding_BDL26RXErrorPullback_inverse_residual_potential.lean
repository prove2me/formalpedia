-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_inverse_residual_potential
-- name    : QEC.Coding.BDL26RXErrorPullback.inverse_residual_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:54:21.345677+00:00
-- url     : https://prove2.me/theorems/ef375839-e1c6-4b42-88c4-72020cab8b06
-- title:
--   BDL26 RXError Pullback: inverse residual potential
-- statement:
--   Extract a full upper degree-zero potential from the actual residual theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L144-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L144-L159

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

theorem QEC.Coding.BDL26RXErrorPullback.inverse_residual_potential (h : i.val % 2 = 0)
    (w : Cocycle (state S (i.val + 1)).presentation) :
    ∃ p : Potential S depth i,
      (indexedFamily S depth).coboundary0 i.succ p = fun q =>
        (((indexedDecoderData S depth).selectedMap i).map1
          (inverseCocycle S depth i h w).val) q - w.val q := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_inverse_residual_potential
-- name    : QEC.Coding.BDL26RZErrorPullback.inverse_residual_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:08:35.665786+00:00
-- url     : https://prove2.me/theorems/a085f6e7-fcea-41bd-b342-021537873d7c
-- title:
--   BDL26 RZError Pullback: inverse residual potential
-- statement:
--   Extract a full upper degree-zero potential from the actual residual theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L129-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L129-L145

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RZCohomology BDL26AlternatingCochain
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RZErrorPullback.inverse_residual_potential (h : ¬ i.val % 2 = 0)
    (w : Cocycle (state S (i.val + 1)).presentation) :
    ∃ p : Potential S depth i,
      (indexedFamily S depth).coboundary0 i.succ p = fun q =>
        (((indexedDecoderData S depth).selectedMap i).map1
          (nextBackwardCocycle S i.val (state S i.val) h w).val) q - w.val q := by sorry

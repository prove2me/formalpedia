-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_inverse_residual_boundary
-- name    : QEC.Coding.BDL26RZErrorPullback.inverse_residual_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:07:37.668752+00:00
-- url     : https://prove2.me/theorems/c7f3db26-1460-4933-b15f-8a1060b2800b
-- title:
--   BDL26 RZError Pullback: inverse residual boundary
-- statement:
--   The actual inverse representative's full discrepancy is an upper boundary.
--   The representative identities use the actual equivalence whose right inverse
--   is proved by `forward_backward_residual_boundary`, including its full potential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L96-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L96-L119

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

theorem QEC.Coding.BDL26RZErrorPullback.inverse_residual_boundary (h : ¬ i.val % 2 = 0)
    (w : Cocycle (state S (i.val + 1)).presentation) :
    (BDL26FiniteCohomology.stepCocycle S i.val
        (nextBackwardCocycle S i.val (state S i.val) h w) :
      Cocycle (state S (i.val + 1)).presentation) - w ∈
      (BDL26RZCohomology.complex (state S (i.val + 1)).presentation).middleCoboundaryInCocycles := by sorry

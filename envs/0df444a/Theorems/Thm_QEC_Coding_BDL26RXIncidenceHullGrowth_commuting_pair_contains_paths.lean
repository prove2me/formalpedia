-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_commuting_pair_contains_paths
-- name    : QEC.Coding.BDL26RXIncidenceHullGrowth.commuting_pair_contains_paths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:40:50.708425+00:00
-- url     : https://prove2.me/theorems/693c6c41-c70b-47b4-ab4b-e714531c5a82
-- title:
--   BDL26 RXIncidence Hull Growth: commuting pair contains paths
-- statement:
--   Every point in a seed component is forced into ANY all-word commuting pair.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L96-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean#L96-L104

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXIncidenceHullGrowth.commuting_pair_contains_paths (h : i.val % 2 = 0)
    (seed A : Finset (state S i.val).presentation.Q)
    (B : Finset (FamilyZ S depth i.succ)) (hseed : seed ⊆ A)
    (commutes : ∀ w, MultiscaleDecoder.maskWord B (nativeDifferential S depth i w) =
      nativeDifferential S depth i (MultiscaleDecoder.maskWord A w))
    {q r : (state S i.val).presentation.Q} (hq : q ∈ seed)
    (path : SharedZPath (state S i.val).presentation q r) : r ∈ A := by sorry

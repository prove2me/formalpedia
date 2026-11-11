-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_le_every_commuting_pair
-- name    : QEC.Coding.BDL26RXDifferentialMasks.incidenceHull_le_every_commuting_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:39:10.725214+00:00
-- url     : https://prove2.me/theorems/8961108e-b5b7-4880-8217-75abf186f8a8
-- title:
--   BDL26 RXDifferential Masks: incidence Hull le every commuting pair
-- statement:
--   Any commuting masks containing the seed must contain the constructed lower
--   hull and its WHOLE two-copy native selected region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L247-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L247-L262

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.incidenceHull_le_every_commuting_pair (h : i.val % 2 = 0)
    (seed A : Finset (state S i.val).presentation.Q)
    (B : Finset (FamilyZ S depth i.succ)) (hseed : seed ⊆ A)
    (hc : ∀ w, maskWord B (nativeDifferential S depth i w) =
      nativeDifferential S depth i (maskWord A w)) :
    incidenceHull S depth i seed ⊆ A ∧
      nativeRegion S depth i h (incidenceHull S depth i seed) ⊆ B := by sorry

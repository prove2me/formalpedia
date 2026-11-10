-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzOldX_incidence_iff
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzOldX_incidence_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:39:04.059955+00:00
-- url     : https://prove2.me/theorems/8f12120b-9a32-413c-a898-cd7bacc716c2
-- title:
--   BDL26 Replacement Cochain Maps: rz Old X incidence iff
-- statement:
--   Exact incidence of a retained old-X copy: one terminal in each incident
--   Q-cylinder, and no Z-local edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1425-L1450
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1425-L1450

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzOldX_incidence_iff
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (copy : Two) (target : RZQ P S) :
    rzXQIncidence P A S (Sum.inr (x, copy)) target = true ↔
      ∃ q : P.Q, ∃ hxq : P.xq x q = true,
        target = Sum.inr ⟨q, rzXQVertex P q x hxq S copy⟩ := by sorry

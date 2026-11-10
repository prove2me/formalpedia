-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_radialGauge_vertical
-- name    : QEC.Coding.BDL26XLocalRadialParity.radialGauge_vertical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:34:53.147608+00:00
-- url     : https://prove2.me/theorems/8bcde4fe-6a03-4ff0-a97d-4454c4150f04
-- title:
--   BDL26 XLocal Radial Parity: radial Gauge vertical
-- statement:
--   The BDL26 XLocal Radial Parity construction uses the radial Gauge vertical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L315-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L315-L342

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.radialGauge_vertical
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field)
    (face : XStarFace P x) (copy : Two) (i : Fin (S.half + 1)) (j : Fin S.half) :
    radialGauge P A x S selected alpha
      (Sum.inl (copy, subdivisionVerticalEdge P x S face i j)) =
      if copy = selected ∧ i.val = 0 ∧ j.val = 0 then
        alpha (faceNeighbor P x face 1) else 0 := by sorry

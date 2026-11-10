-- Prove2me | Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_state_face_card_upper
-- name    : QEC.Coding.BDL26QuantitativeBounds.state_face_card_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:45:42.769227+00:00
-- url     : https://prove2.me/theorems/cac17175-58b3-43d5-8515-3baccf4e3b78
-- title:
--   BDL26 Quantitative Bounds: state face card upper
-- statement:
--   Finite face growth from the actual four-face seed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L391-L402
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QuantitativeBounds.lean#L391-L402

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph

theorem QEC.Coding.BDL26QuantitativeBounds.state_face_card_upper (S : OddScale) (n : Nat) :
    Fintype.card (state S n).presentation.Face ≤ 4 * faceGrowthFactor S ^ n := by sorry

-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_face_two_calls
-- name    : QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.face_two_calls
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:56:10.569316+00:00
-- url     : https://prove2.me/theorems/e7ffe49a-aa5b-455c-b36f-3ff58fca6875
-- title:
--   BDL26 Level Two Local Branch Endpoint: face two calls
-- statement:
--   Arbitrary actual nonzero/zero backgrounds, with every Z-face coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L521-L526
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L521-L526

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators
open scoped Classical

theorem QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.face_two_calls (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S) (s t : Syndrome S)
    (hh : supported S (.inl (.inl ⟨z,f⟩)) h) (hd : delta S h=s+t)
    (hs : localSuccess S s) (ht : localSuccess S t) :
    ∃ p : Potential S, boundary S p=h+D S s+D S t := by sorry

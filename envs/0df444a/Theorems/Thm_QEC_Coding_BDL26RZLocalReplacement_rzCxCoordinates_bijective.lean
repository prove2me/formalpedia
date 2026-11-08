-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzCxCoordinates_bijective
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzCxCoordinates_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:04:04.351509+00:00
-- url     : https://prove2.me/theorems/d3419b2f-fff3-4658-b75e-51735a685e1d
-- title:
--   BDL26 RZLocal Replacement: rz Cx Coordinates bijective
-- statement:
--   The BDL26 RZLocal Replacement construction uses the rz Cx Coordinates bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16039-L16048
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16039-L16048

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzCxCoordinates_bijective : Function.Bijective rzCxCoordinates := by sorry

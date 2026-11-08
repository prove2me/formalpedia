-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzQ_card
-- name    : QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzQ_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:53:05.682516+00:00
-- url     : https://prove2.me/theorems/80885299-cd11-4d85-a7e1-717405343787
-- title:
--   BDL26 RZLocal Replacement: base Scale Five rz Q card
-- statement:
--   The BDL26 RZLocal Replacement construction uses the base Scale Five rz Q card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17321-L17326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17321-L17326

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
attribute [instance] baseScaleFiveRzXFintype baseScaleFiveRzQFintype
  baseScaleFiveRzZFintype baseScaleFiveRzFaceFintype
set_option maxRecDepth 10000

theorem QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzQ_card :
    Fintype.card (RZQ baseTannerSquarePresentation scaleFive) = 140 := by sorry

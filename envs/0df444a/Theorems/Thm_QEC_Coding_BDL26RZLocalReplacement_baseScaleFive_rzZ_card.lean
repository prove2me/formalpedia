-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzZ_card
-- name    : QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzZ_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:01:04.038201+00:00
-- url     : https://prove2.me/theorems/5118e477-c00b-4e7e-b185-c98aad8c378b
-- title:
--   BDL26 RZLocal Replacement: base Scale Five rz Z card
-- statement:
--   The BDL26 RZLocal Replacement construction uses the base Scale Five rz Z card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17328-L17332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17328-L17332

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

theorem QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzZ_card :
    Fintype.card (RZZ baseTannerSquarePresentation scaleFive) = 60 := by sorry

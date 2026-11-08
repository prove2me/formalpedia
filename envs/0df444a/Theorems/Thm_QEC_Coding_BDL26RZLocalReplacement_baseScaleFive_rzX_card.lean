-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_baseScaleFive_rzX_card
-- name    : QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzX_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:51:48.444694+00:00
-- url     : https://prove2.me/theorems/597591fc-d233-4ce6-8bdd-cd6c1ec77312
-- title:
--   BDL26 RZLocal Replacement: base Scale Five rz X card
-- statement:
--   The BDL26 RZLocal Replacement construction uses the base Scale Five rz X card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17314-L17318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L17314-L17318

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

theorem QEC.Coding.BDL26RZLocalReplacement.baseScaleFive_rzX_card :
    Fintype.card (RZX baseTannerSquarePresentation scaleFive) = 82 := by sorry

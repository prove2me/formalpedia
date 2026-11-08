-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_base_qzIncidenceMatrix_eq
-- name    : QEC.Coding.BDL26FiniteTannerSquare.base_qzIncidenceMatrix_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:25:12.790751+00:00
-- url     : https://prove2.me/theorems/e2cfd8f4-48ec-4c6e-a8db-ff4152ea6ddf
-- title:
--   BDL26 Finite Tanner Square: base qz Incidence Matrix eq
-- statement:
--   The BDL26 Finite Tanner Square construction uses the base qz Incidence Matrix eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L544-L549
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean#L544-L549

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open BDL26FiniteAlternatingCore
open Module
attribute [instance] TannerSquareData.xFintype TannerSquareData.qFintype
  TannerSquareData.zFintype TannerSquareData.faceFintype
  TannerSquareData.xDecidableEq TannerSquareData.qDecidableEq
  TannerSquareData.zDecidableEq TannerSquareData.faceDecidableEq

theorem QEC.Coding.BDL26FiniteTannerSquare.base_qzIncidenceMatrix_eq :
    qzIncidenceMatrix baseTannerSquarePresentation = baseBoundary2Matrix := by sorry

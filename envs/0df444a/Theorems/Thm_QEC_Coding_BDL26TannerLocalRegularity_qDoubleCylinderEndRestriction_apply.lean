-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qDoubleCylinderEndRestriction_apply
-- name    : QEC.Coding.BDL26TannerLocalRegularity.qDoubleCylinderEndRestriction_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:32:07.296819+00:00
-- url     : https://prove2.me/theorems/c9c00b46-9dc3-4096-84f0-97ebe81ad42c
-- title:
--   BDL26 Tanner Local Regularity: q Double Cylinder End Restriction apply
-- statement:
--   The BDL26 Tanner Local Regularity construction uses the q Double Cylinder End Restriction apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3149-L3154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3149-L3154

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26TannerLocalRegularity
open Module
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
universe u

theorem QEC.Coding.BDL26TannerLocalRegularity.qDoubleCylinderEndRestriction_apply
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) (endIndex : Two)
    (word : Word Field (QDoubleCylinderVertex P q S))
    (vertex : QSubdivisionVertex P q S) :
    qDoubleCylinderEndRestriction P q S endIndex word vertex =
      word (endIndex, vertex) := by sorry

attribute [defeq] QEC.Coding.BDL26TannerLocalRegularity.qDoubleCylinderEndRestriction_apply

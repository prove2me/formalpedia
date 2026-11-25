-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_eq_natCast_of_add_one_eq_8a51e7536497
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_eq_natCast_of_add_one_eq_8a51e7536497
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:12:52.461136+00:00
-- url     : https://prove2.me/theorems/aa1c9d67-c8d7-40b0-aeba-e3bcc511b0cc
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Dim eq nat Cast of add one eq 8a51e7536497: P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Dim eq nat Cast of add one eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Dim eq nat Cast of add one eq 8a51e7536497 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Generic Fibre Dim eq nat Cast of add one eq 8a51e7536497 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreDim.lean#L39-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreDim.lean#L39-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGenericFibreDim
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)
open GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_eq_natCast_of_add_one_eq_8a51e7536497 (d : ℕ) (x : WithBot ℕ∞)
    (hform : x + 1 = ((d : ℕ) : WithBot ℕ∞) + 1) : x = d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«GenericFibreDim».«eq_natCast_of_add_one_eq» := P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_eq_natCast_of_add_one_eq_8a51e7536497

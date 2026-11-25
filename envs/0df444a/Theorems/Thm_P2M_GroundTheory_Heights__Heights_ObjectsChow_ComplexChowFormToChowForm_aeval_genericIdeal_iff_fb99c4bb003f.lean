-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_aeval_genericIdeal_iff_fb99c4bb003f
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_aeval_genericIdeal_iff_fb99c4bb003f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:12:45.390871+00:00
-- url     : https://prove2.me/theorems/d2048f6f-4b4e-4a4b-adfe-56b3f91ca223
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Complex Chow Form To Chow Form aeval generic Ideal iff fb99c4bb003f: P2 M Ground Theory Heights  Heights Objects Chow Complex Chow Form To Chow Form ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Complex Chow Form To Chow Form aeval generic Ideal iff fb99c4bb003f construction uses the P2 M Ground Theory Heights  Heights Objects Chow Complex Chow Form To Chow Form aeval generic Ideal iff fb99c4bb003f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/AevalGenericIdealIff.lean#L50-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/AevalGenericIdealIff.lean#L50-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coeff_coordPoly_539797cde10d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_C_mul_map_9d8219af7fc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_mem_of_mem_map_75eab8a0118b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_sum_8ff9631ad41f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_incidenceIdeal_map_8d93a5362789
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_mem_zeroLocus_incidenceIdeal_a3506a649f6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_radical_map_eq_9ece7ec07417
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_sum_coordPoly_903079f12110
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_vanishes_incidence_iff_796d408552b0

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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk conePts)
open ChowFormExtend (incidenceIdeal coordPoly coeff_coordPoly coordPoly_C_mul_map coordPoly_mem_of_mem_map
  mem_zeroLocus_incidenceIdeal vanishes_incidence_iff incidenceIdeal_map radical_map_eq coordSupport
  sum_coordPoly coordPoly_sum)
open GroundTheory.Heights₂.Heights.ObjectsChow.ComplexChowFormToChowForm
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_aeval_genericIdeal_iff_fb99c4bb003f (P : Ideal (MRing (PBlk n))) (x : Fin n → ℂ) :
    (∀ q ∈ (genericIdeal P).map (map (algebraMap ℚ ℂ)), aeval x q = 0) ↔
      ∀ h ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P, eval x (map (Int.castRingHom ℂ) h) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«ComplexChowFormToChowForm».«aeval_genericIdeal_iff» := P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_aeval_genericIdeal_iff_fb99c4bb003f

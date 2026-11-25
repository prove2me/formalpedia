-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_exists_coeff_eq_apply_9b6b5e589617
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_exists_coeff_eq_apply_9b6b5e589617
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:27.528694+00:00
-- url     : https://prove2.me/theorems/0fbeecf6-81b0-5bac-8dca-115f9e86d865
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow exists coeff eq apply 9b6b5e589617: P2 M Ground Theory Heights  Heights Objects Chow exists coeff eq apply 9b6b5e589617
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow exists coeff eq apply 9b6b5e589617 construction uses the P2 M Ground Theory Heights  Heights Objects Chow exists coeff eq apply 9b6b5e589617 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PIntChowFormExists.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PIntChowFormExists.lean#L20-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGenericFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PAffineChartTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIntChowFormExists
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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_exists_coeff_eq_apply_9b6b5e589617 {σ R S : Type*} [CommSemiring R] [CommSemiring S] (F : R → S) (hF : F 0 = 0)
    (p : MvPolynomial σ R) : ∃ q : MvPolynomial σ S, ∀ m, coeff m q = F (coeff m p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«exists_coeff_eq_apply» := P2M_GroundTheory_Heights__Heights_ObjectsChow_exists_coeff_eq_apply_9b6b5e589617

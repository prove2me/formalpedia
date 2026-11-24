-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_iff_0f52654b96e9
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_iff_0f52654b96e9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:05.8398+00:00
-- url     : https://prove2.me/theorems/aff067dd-177c-4f61-bc64-8aa50769ccca
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow is Multi Homog iff 0f52654b96e9: P2 M Ground Theory Heights  Heights Objects Chow is Multi Homog iff 0f52654b96e9
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow is Multi Homog iff 0f52654b96e9 construction uses the P2 M Ground Theory Heights  Heights Objects Chow is Multi Homog iff 0f52654b96e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L53-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_iff_0f52654b96e9 {R : Type*} [CommSemiring R] {e δ : ℕ}
    (f : MvPolynomial (Fin (e + 1) × Fin n) R) : IsMultiHomog δ f ↔ IsMultihomog f δ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«isMultiHomog_iff» := P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_iff_0f52654b96e9

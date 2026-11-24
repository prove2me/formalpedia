-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_of_isChowForm_129f76209172
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_of_isChowForm_129f76209172
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:50.990632+00:00
-- url     : https://prove2.me/theorems/f9afe8a8-d9d6-434b-a009-0b11ce5f3ae7
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow is Multi Homog of is Chow Form 129f76209172: P2 M Ground Theory Heights  Heights Objects Chow is Multi Homog of is Chow Form 129f76209172
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow is Multi Homog of is Chow Form 129f76209172 construction uses the P2 M Ground Theory Heights  Heights Objects Chow is Multi Homog of is Chow Form 129f76209172 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L63-L67

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_of_isChowForm_129f76209172 {e δ : ℕ} {P : Ideal (MRing (PBlk n))}
    {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f)) : IsMultiHomog δ f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«isMultiHomog_of_isChowForm» := P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_of_isChowForm_129f76209172

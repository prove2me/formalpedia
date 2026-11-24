-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isChowForm_C_mul_941588753c43
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_isChowForm_C_mul_941588753c43
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:23.780937+00:00
-- url     : https://prove2.me/theorems/9f64b8e8-ddd1-4027-9a5b-60b62cff7516
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow is Chow Form C mul 941588753c43: P2 M Ground Theory Heights  Heights Objects Chow is Chow Form C mul 941588753c43
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow is Chow Form C mul 941588753c43 construction uses the P2 M Ground Theory Heights  Heights Objects Chow is Chow Form C mul 941588753c43 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L81-L86

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_isChowForm_C_mul_941588753c43 {F : Type*} [Field F] {I : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) {c : F} (hc : c ≠ 0) :
    IsChowForm I k (C c * f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«isChowForm_C_mul» := P2M_GroundTheory_Heights__Heights_ObjectsChow_isChowForm_C_mul_941588753c43

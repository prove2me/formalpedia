-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsMultiHomog_specFirst_e9679426b5b5
-- name    : P2M_GroundTheory_Heights__Heights_IsMultiHomog_specFirst_e9679426b5b5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:57.123257+00:00
-- url     : https://prove2.me/theorems/bc1e9fa3-9197-4a1a-9294-661e4dbf0020
-- title:
--   P2 M Ground Theory Heights  Heights Is Multi Homog spec First e9679426b5b5: P2 M Ground Theory Heights  Heights Is Multi Homog spec First e9679426b5b5
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Multi Homog spec First e9679426b5b5 construction uses the P2 M Ground Theory Heights  Heights Is Multi Homog spec First e9679426b5b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L51-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L51-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {R : Type*} [CommRing R]
variable {k n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IsMultiHomog_specFirst_e9679426b5b5 {δ : ℕ} {f : MvPolynomial (Fin (k + 1) × Fin n) R}
    (hf : IsMultiHomog δ f) (u : Fin n → R) : IsMultiHomog δ (specFirst f u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsMultiHomog».«specFirst» := P2M_GroundTheory_Heights__Heights_IsMultiHomog_specFirst_e9679426b5b5

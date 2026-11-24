-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_jacobiTheta__add_int_mul_6ed98b2144e6
-- name    : P2M_GroundTheory_Heights__Heights_KeyFormula_jacobiTheta__add_int_mul_6ed98b2144e6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:18.40808+00:00
-- url     : https://prove2.me/theorems/d2570ad1-1924-4cf8-bfb2-f778be4dc669
-- title:
--   P2 M Ground Theory Heights  Heights Key Formula jacobi Theta  add int mul 6ed98b2144e6: P2 M Ground Theory Heights  Heights Key Formula jacobi Theta  add int mul 6ed98b2144e6
-- statement:
--   The P2 M Ground Theory Heights  Heights Key Formula jacobi Theta  add int mul 6ed98b2144e6 construction uses the P2 M Ground Theory Heights  Heights Key Formula jacobi Theta  add int mul 6ed98b2144e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/RigSymFormTauINontrivial.lean#L125-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/RigSymFormTauINontrivial.lean#L125-L141

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Matrix Real
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_KeyFormula_jacobiTheta__add_int_mul_6ed98b2144e6 (w τ : ℂ) (k : ℤ) :
    jacobiTheta₂ (w + k * τ) τ = cexp (-(π * I * k ^ 2 * τ) - 2 * π * I * k * w) * jacobiTheta₂ w τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KeyFormula».«jacobiTheta₂_add_int_mul» := P2M_GroundTheory_Heights__Heights_KeyFormula_jacobiTheta__add_int_mul_6ed98b2144e6

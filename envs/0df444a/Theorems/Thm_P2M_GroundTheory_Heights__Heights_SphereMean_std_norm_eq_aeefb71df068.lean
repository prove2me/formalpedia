-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_std_norm_eq_aeefb71df068
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_std_norm_eq_aeefb71df068
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:41.950807+00:00
-- url     : https://prove2.me/theorems/7f4868ce-5a1c-431d-8dfe-9ce449e799b2
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean std norm eq aeefb71df068: P2 M Ground Theory Heights  Heights Sphere Mean std norm eq aeefb71df068
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean std norm eq aeefb71df068 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean std norm eq aeefb71df068 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMean.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMean.lean#L59-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
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
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean

theorem P2M_GroundTheory_Heights__Heights_SphereMean_std_norm_eq_aeefb71df068 (n : ℕ) (v : Fin n → ℂ) : (HermNorm.std n).norm v = √(sqNorm v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«std_norm_eq» := P2M_GroundTheory_Heights__Heights_SphereMean_std_norm_eq_aeefb71df068

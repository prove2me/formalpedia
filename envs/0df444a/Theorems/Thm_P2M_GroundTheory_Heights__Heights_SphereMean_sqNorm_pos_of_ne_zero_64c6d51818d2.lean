-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_pos_of_ne_zero_64c6d51818d2
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_pos_of_ne_zero_64c6d51818d2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:55.466799+00:00
-- url     : https://prove2.me/theorems/60b51d4e-7bcb-4e92-afbe-4c7e2e8de2d0
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean sq Norm pos of ne zero 64c6d51818d2: P2 M Ground Theory Heights  Heights Sphere Mean sq Norm pos of ne zero 64c6d51818d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean sq Norm pos of ne zero 64c6d51818d2 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean sq Norm pos of ne zero 64c6d51818d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L119-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L119-L127

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_pos_of_ne_zero_64c6d51818d2 {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) : 0 < sqNorm x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«sqNorm_pos_of_ne_zero» := P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_pos_of_ne_zero_64c6d51818d2

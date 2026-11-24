-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_isOpen_ballSet_4b2e1ed44a1c
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_isOpen_ballSet_4b2e1ed44a1c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:16.955527+00:00
-- url     : https://prove2.me/theorems/6fefeeba-e7e6-4d9c-a794-9b176b95cf72
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean is Open ball Set 4b2e1ed44a1c: P2 M Ground Theory Heights  Heights Sphere Mean is Open ball Set 4b2e1ed44a1c
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean is Open ball Set 4b2e1ed44a1c construction uses the P2 M Ground Theory Heights  Heights Sphere Mean is Open ball Set 4b2e1ed44a1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L62-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
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
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean

theorem P2M_GroundTheory_Heights__Heights_SphereMean_isOpen_ballSet_4b2e1ed44a1c (n : ℕ) (s : ℝ) : IsOpen (ballSet n s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«isOpen_ballSet» := P2M_GroundTheory_Heights__Heights_SphereMean_isOpen_ballSet_4b2e1ed44a1c

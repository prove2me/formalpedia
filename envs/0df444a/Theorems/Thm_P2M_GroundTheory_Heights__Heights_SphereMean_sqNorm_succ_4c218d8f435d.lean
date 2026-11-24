-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_succ_4c218d8f435d
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_succ_4c218d8f435d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:01.184329+00:00
-- url     : https://prove2.me/theorems/4d17da62-f80f-4acd-aabd-e087ee79ac84
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean sq Norm succ 4c218d8f435d: P2 M Ground Theory Heights  Heights Sphere Mean sq Norm succ 4c218d8f435d
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean sq Norm succ 4c218d8f435d construction uses the P2 M Ground Theory Heights  Heights Sphere Mean sq Norm succ 4c218d8f435d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L15-L17

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_succ_4c218d8f435d {m : ℕ} (x : Fin (m + 1) → ℂ) :
    sqNorm x = ‖x 0‖ ^ 2 + sqNorm (Fin.tail x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«sqNorm_succ» := P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_succ_4c218d8f435d

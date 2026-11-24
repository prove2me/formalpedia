-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_smul_0f1c388bb826
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_smul_0f1c388bb826
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:33.894799+00:00
-- url     : https://prove2.me/theorems/c83d7805-2d88-44e9-a5c6-c75e3305e6ca
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean sq Norm smul 0f1c388bb826: P2 M Ground Theory Heights  Heights Sphere Mean sq Norm smul 0f1c388bb826
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean sq Norm smul 0f1c388bb826 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean sq Norm smul 0f1c388bb826 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L68-L69

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_smul_0f1c388bb826 {n : ℕ} (c : ℝ) (x : Fin n → ℂ) : sqNorm (c • x) = c ^ 2 * sqNorm x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«sqNorm_smul» := P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_smul_0f1c388bb826

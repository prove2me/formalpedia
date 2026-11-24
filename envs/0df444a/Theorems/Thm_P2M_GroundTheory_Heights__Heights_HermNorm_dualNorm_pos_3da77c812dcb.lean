-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_pos_3da77c812dcb
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_pos_3da77c812dcb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:38.024867+00:00
-- url     : https://prove2.me/theorems/9e1edb91-ee39-4047-aa24-dd954b452314
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm dual Norm pos 3da77c812dcb: P2 M Ground Theory Heights  Heights Herm Norm dual Norm pos 3da77c812dcb
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm dual Norm pos 3da77c812dcb construction uses the P2 M Ground Theory Heights  Heights Herm Norm dual Norm pos 3da77c812dcb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLogBound.lean#L31-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLogBound.lean#L31-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
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
open MvPolynomial MeasureTheory NumberField Matrix
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_pos_3da77c812dcb (h : HermNorm n) {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < h.dualNorm y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«dualNorm_pos» := P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_pos_3da77c812dcb

-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_pointOf_eq_zero_1a71672ffe50
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_pointOf_eq_zero_1a71672ffe50
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:39.424798+00:00
-- url     : https://prove2.me/theorems/361d2b18-e044-4c6b-a507-7d662a76fbae
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm point Of eq zero 1a71672ffe50: P2 M Ground Theory Heights  Heights Herm Norm point Of eq zero 1a71672ffe50
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm point Of eq zero 1a71672ffe50 construction uses the P2 M Ground Theory Heights  Heights Herm Norm point Of eq zero 1a71672ffe50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeIntegralLine.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeIntegralLine.lean#L17-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermNorm_pointOf_eq_zero_1a71672ffe50 (h : HermNorm n) {y : EuclideanSpace ℂ (Fin n)}
    (hy : h.pointOf y = 0) : y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«pointOf_eq_zero» := P2M_GroundTheory_Heights__Heights_HermNorm_pointOf_eq_zero_1a71672ffe50

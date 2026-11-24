-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionSmall_mkF_den_ne_zero_3d31e6ab25c8
-- name    : P2M_GroundTheory_Heights__Heights_SectionSmall_mkF_den_ne_zero_3d31e6ab25c8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:06.041219+00:00
-- url     : https://prove2.me/theorems/de3ead43-28a6-43e6-b2d5-95f275261539
-- title:
--   P2 M Ground Theory Heights  Heights Section Small mk F den ne zero 3d31e6ab25c8: P2 M Ground Theory Heights  Heights Section Small mk F den ne zero 3d31e6ab25c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Small mk F den ne zero 3d31e6ab25c8 construction uses the P2 M Ground Theory Heights  Heights Section Small mk F den ne zero 3d31e6ab25c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PSectionSmall.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PSectionSmall.lean#L15-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PSectionSmall
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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionSmall

theorem P2M_GroundTheory_Heights__Heights_SectionSmall_mkF_den_ne_zero_3d31e6ab25c8 {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a) :
    P.mkF s.den ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionSmall».«mkF_den_ne_zero» := P2M_GroundTheory_Heights__Heights_SectionSmall_mkF_den_ne_zero_3d31e6ab25c8

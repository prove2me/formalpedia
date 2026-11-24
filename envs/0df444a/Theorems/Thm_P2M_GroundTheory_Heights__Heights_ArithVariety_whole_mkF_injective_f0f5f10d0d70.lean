-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_whole_mkF_injective_f0f5f10d0d70
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_whole_mkF_injective_f0f5f10d0d70
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:48.97871+00:00
-- url     : https://prove2.me/theorems/1f688145-6d33-4457-bacc-37d9d5ade7db
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety whole mk F injective f0f5f10d0d70: P2 M Ground Theory Heights  Heights Arith Variety whole mk F injective f0f5f10d0d70
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety whole mk F injective f0f5f10d0d70 construction uses the P2 M Ground Theory Heights  Heights Arith Variety whole mk F injective f0f5f10d0d70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L37-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open GroundTheory.Heights₂.Heights.ArithVariety
variable (n : ι → ℕ)
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_whole_mkF_injective_f0f5f10d0d70 : Function.Injective (whole n).mkF := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«whole_mkF_injective» := P2M_GroundTheory_Heights__Heights_ArithVariety_whole_mkF_injective_f0f5f10d0d70

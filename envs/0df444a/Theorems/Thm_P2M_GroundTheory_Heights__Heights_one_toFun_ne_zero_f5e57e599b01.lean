-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_one_toFun_ne_zero_f5e57e599b01
-- name    : P2M_GroundTheory_Heights__Heights_one_toFun_ne_zero_f5e57e599b01
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:16.974178+00:00
-- url     : https://prove2.me/theorems/c6f03f90-cc9c-57a5-bbfb-391e1f182c22
-- title:
--   P2 M Ground Theory Heights  Heights one to Fun ne zero f5e57e599b01: P2 M Ground Theory Heights  Heights one to Fun ne zero f5e57e599b01
-- statement:
--   The P2 M Ground Theory Heights  Heights one to Fun ne zero f5e57e599b01 construction uses the P2 M Ground Theory Heights  Heights one to Fun ne zero f5e57e599b01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L193-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L193-L196

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
variable (n : ι → ℕ) (k₀ : ι)

theorem P2M_GroundTheory_Heights__Heights_one_toFun_ne_zero_f5e57e599b01 (P : ArithVariety n) : (IntegralSection.one P).toFun ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«one_toFun_ne_zero» := P2M_GroundTheory_Heights__Heights_one_toFun_ne_zero_f5e57e599b01

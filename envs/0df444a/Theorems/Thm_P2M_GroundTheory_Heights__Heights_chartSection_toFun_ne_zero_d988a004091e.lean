-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartSection_toFun_ne_zero_d988a004091e
-- name    : P2M_GroundTheory_Heights__Heights_chartSection_toFun_ne_zero_d988a004091e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:16.962052+00:00
-- url     : https://prove2.me/theorems/f7aa06ce-a463-47fa-956e-6a73547a48b1
-- title:
--   P2 M Ground Theory Heights  Heights chart Section to Fun ne zero d988a004091e: P2 M Ground Theory Heights  Heights chart Section to Fun ne zero d988a004091e
-- statement:
--   The P2 M Ground Theory Heights  Heights chart Section to Fun ne zero d988a004091e construction uses the P2 M Ground Theory Heights  Heights chart Section to Fun ne zero d988a004091e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L162-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L162-L168

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

theorem P2M_GroundTheory_Heights__Heights_chartSection_toFun_ne_zero_d988a004091e (c : (k : ι) → Fin (n k + 1)) :
    (IntegralSection.chartSection (ArithVariety.whole n) c).toFun ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chartSection_toFun_ne_zero» := P2M_GroundTheory_Heights__Heights_chartSection_toFun_ne_zero_d988a004091e

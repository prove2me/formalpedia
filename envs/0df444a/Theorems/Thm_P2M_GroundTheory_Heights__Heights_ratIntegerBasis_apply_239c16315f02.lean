-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ratIntegerBasis_apply_239c16315f02
-- name    : P2M_GroundTheory_Heights__Heights_ratIntegerBasis_apply_239c16315f02
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:51.963167+00:00
-- url     : https://prove2.me/theorems/6a7c49b3-63ae-47bd-a37c-e65d8f66fe22
-- title:
--   P2 M Ground Theory Heights  Heights rat Integer Basis apply 239c16315f02: P2 M Ground Theory Heights  Heights rat Integer Basis apply 239c16315f02
-- statement:
--   The P2 M Ground Theory Heights  Heights rat Integer Basis apply 239c16315f02 construction uses the P2 M Ground Theory Heights  Heights rat Integer Basis apply 239c16315f02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L222-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L222-L223

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

theorem P2M_GroundTheory_Heights__Heights_ratIntegerBasis_apply_239c16315f02 (a : Fin (0 + 1)) : ((ratIntegerBasis a : 𝓞 ℚ) : ℚ) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ratIntegerBasis_apply» := P2M_GroundTheory_Heights__Heights_ratIntegerBasis_apply_239c16315f02

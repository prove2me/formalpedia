-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_incidence_mono_64f19830bda4
-- name    : P2M_GroundTheory_Heights__Heights_incidence_mono_64f19830bda4
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:09.04746+00:00
-- url     : https://prove2.me/theorems/217b775a-325f-4f2f-b3a2-52d81fe1630f
-- title:
--   P2 M Ground Theory Heights  Heights incidence mono 64f19830bda4: P2 M Ground Theory Heights  Heights incidence mono 64f19830bda4
-- statement:
--   The P2 M Ground Theory Heights  Heights incidence mono 64f19830bda4 construction uses the P2 M Ground Theory Heights  Heights incidence mono 64f19830bda4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormReduced.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormReduced.lean#L22-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncIdealSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormReduced
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
variable {F : Type*} [Field F] {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_incidence_mono_64f19830bda4 {I W : Ideal (MvPolynomial (Fin n) F)} (hIW : I ≤ W)
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence W k) : u ∈ incidence I k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«incidence_mono» := P2M_GroundTheory_Heights__Heights_incidence_mono_64f19830bda4

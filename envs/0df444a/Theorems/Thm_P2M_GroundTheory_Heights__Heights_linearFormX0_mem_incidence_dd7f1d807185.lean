-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linearFormX0_mem_incidence_dd7f1d807185
-- name    : P2M_GroundTheory_Heights__Heights_linearFormX0_mem_incidence_dd7f1d807185
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:53.369288+00:00
-- url     : https://prove2.me/theorems/ef00326f-39e7-4d30-ae3b-0ef7cf8ca5c8
-- title:
--   P2 M Ground Theory Heights  Heights linear Form X0 mem incidence dd7f1d807185: P2 M Ground Theory Heights  Heights linear Form X0 mem incidence dd7f1d807185
-- statement:
--   The P2 M Ground Theory Heights  Heights linear Form X0 mem incidence dd7f1d807185 construction uses the P2 M Ground Theory Heights  Heights linear Form X0 mem incidence dd7f1d807185 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsIncidenceZeroLocus.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsIncidenceZeroLocus.lean#L40-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
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
attribute [local instance] MvPolynomial.gradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_linearFormX0_mem_incidence_dd7f1d807185 :
    linearFormX0 (AlgebraicClosure ℚ) ∈ incidence (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linearFormX0_mem_incidence» := P2M_GroundTheory_Heights__Heights_linearFormX0_mem_incidence_dd7f1d807185
